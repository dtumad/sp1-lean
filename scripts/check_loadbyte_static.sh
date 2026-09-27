#!/usr/bin/env bash
# Explicit setup only: this runner never installs dependencies or toolchains.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
if [[ $# != 0 ]]; then
  echo 'usage: scripts/check_loadbyte_static.sh' >&2
  exit 2
fi
for prerequisite in git python3 elan; do
  if ! command -v "$prerequisite" >/dev/null 2>&1; then
    echo "Missing $prerequisite; see docs/loadbyte-static.md for setup." >&2
    exit 2
  fi
done
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}
python3 - <<'PY'
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

root = Path.cwd()
out = root / '.lake/build/loadbyte-static'
out.mkdir(parents=True, exist_ok=True)
manifest = json.loads(Path('lake-manifest.json').read_text())
toolchain = Path('lean-toolchain').read_text().strip()
def git(*args):
    return subprocess.check_output(['git', *args], text=True).strip()

def source_digest():
    files = subprocess.check_output(['git', 'ls-files', '-z', '--cached', '--others',
                                     '--exclude-standard']).split(b'\0')
    digest = hashlib.sha256()
    for filename in sorted(set(files) - {b''}):
        path = Path(os.fsdecode(filename))
        digest.update(filename + b'\0')
        if path.is_symlink():
            digest.update(b'link\0' + os.fsencode(os.readlink(path)))
        elif path.is_file():
            digest.update(str(path.stat().st_mode & 0o777).encode() + b'\0' + path.read_bytes())
        else:
            digest.update(b'missing')
        digest.update(b'\0')
    return digest.hexdigest()

provenance = {
    'capturedAtUtc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'revision': git('rev-parse', 'HEAD'),
    'sourceStatusBefore': git('status', '--porcelain', '--untracked-files=normal'),
    'sourceDigestBefore': source_digest(),
    'toolchain': toolchain,
    'dependencies': manifest['packages'],
    'cache': {
        'projectBuildDirectoryExisted': (root / '.lake/build/lib/lean').exists(),
        'description': 'Uses prepared pinned checkouts and any existing project/dependency artifacts; no cold-build claim.'
    },
    'ci': {key: os.environ.get(key) for key in
           ['GITHUB_ACTIONS', 'GITHUB_REPOSITORY', 'GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT',
            'GITHUB_SHA', 'GITHUB_REF', 'GITHUB_EVENT_NAME', 'SP1_LOADBYTE_PR_HEAD']},
    'status': 'running',
}
provenance['dirty'] = bool(provenance['sourceStatusBefore'])
(out / 'provenance.json').write_text(json.dumps(provenance, indent=2) + '\n')
(out / 'commands.log').write_text('')

def run(command):
    start = time.monotonic()
    result = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    entry = {'command': command, 'seconds': round(time.monotonic() - start, 3),
             'exitCode': result.returncode, 'stdout': result.stdout, 'stderr': result.stderr}
    with (out / 'commands.log').open('a') as stream:
        stream.write(json.dumps(entry) + '\n')
    if result.returncode:
        raise RuntimeError(f"Command failed ({result.returncode}): {command}\n{result.stdout}\n{result.stderr}")
    return result

try:
    version = run(['elan', 'run', toolchain, 'lean', '--version'])
    provenance['leanVersion'] = version.stdout.strip()
    by_name = {package['name']: package for package in manifest['packages']}
    for block in re.split(r'\[\[require\]\]', Path('lakefile.toml').read_text())[1:]:
        body = re.split(r'\n\[\[', block)[0]
        name = re.search(r'^name = "([^"]+)"', body, re.M)
        revision = re.search(r'^rev = "([^"]+)"', body, re.M)
        url = re.search(r'^git = "([^"]+)"', body, re.M)
        if name and revision and url:
            resolved = by_name.get(name[1], {})
            if (revision[1] not in (resolved.get('inputRev'), resolved.get('rev')) or
                    url[1] != resolved.get('url')):
                raise RuntimeError(f'{name[1]}: Lake configuration and resolved pin disagree')
    for package in manifest['packages']:
        directory = Path(manifest['packagesDir']) / package['name']
        if package['type'] != 'git' or not (directory / '.git').exists():
            raise RuntimeError(f"Missing pinned {package['name']}; prepare dependencies explicitly")
        if git('-C', str(directory), 'rev-parse', 'HEAD') != package['rev']:
            raise RuntimeError(f"Wrong revision for {package['name']}; prepare pinned dependencies explicitly")
        if git('-C', str(directory), 'status', '--porcelain', '--untracked-files=no'):
            raise RuntimeError(f"Tracked dependency edits in {package['name']}")
    run(['elan', 'run', toolchain, 'lake', '--no-cache', 'build', '--wfail', '--iofail',
         'SP1CleanTest.Alignment.Examples.LoadByteStatic'])
    result = run(['elan', 'run', toolchain, 'lake', 'env', 'lean', 'scripts/loadByteStatic.lean'])
    if result.stderr:
        raise RuntimeError('Unexpected driver stderr: ' + result.stderr)
    report = json.loads(result.stdout)
    expected = [f'{op}/offset-{offset}/byte-{value}' for op in ['LB', 'LBU']
                for offset in range(8) for value in [0, 127, 128, 255]]
    expected += ['inactive-byte-300', 'same-key-reader-demand', 'wrong-low-byte',
                 'wrong-selectors', 'active-out-of-range']
    if ([case['id'] for case in report['cases']] != expected or
            [case['expected'] for case in report['cases']] != [True] * 66 + [False] * 3 or
            not all(case['passed'] is True and type(case['expected']) is bool and
                    type(case['actual']) is bool and case['expected'] == case['actual']
                    for case in report['cases']) or
            report['oldByteBalanced'] is not True or report['newByteBalanced'] is not True):
        raise RuntimeError('Missing, duplicated, reordered or failing regression case')
    if (report['fixedTableRows'] != 256 or report['activeRows'] != 64 or
            report['inactiveRows'] != 1 or report['oldDedicatedProviderRows'] != 65 or
            report['newDedicatedProviderRows'] != 0):
        raise RuntimeError('Unexpected workload or fixed-table inventory')
    (out / 'results.json').write_text(result.stdout)
    declarations = [
        'SP1Clean.LoadByteStaticChip.soundness',
        'SP1Clean.LoadByteStaticChip.completeness',
        'SP1Clean.LoadByteStaticChip.buildRow_eq_original',
        'SP1Clean.LoadByteStaticChip.fixedByte_contains_iff',
        'SP1Clean.LoadByteStaticChip.gated_fixedByte_iff',
        'SP1Clean.LoadByteStaticChip.interactions_perm',
        'SP1Clean.LoadByteStaticChip.constraints_iff',
        'SP1Clean.LoadByteStaticChip.inactive_constraints_iff',
        'SP1Clean.LoadByteStaticChip.traceTable_constraints',
        'SP1Clean.Soundness.LoadByteStatic.selected_pair_balance',
        'SP1Clean.Soundness.LoadByteStatic.providerRow_interactions',
        'SP1Clean.Soundness.LoadByteStatic.assembly_interactions_perm',
        'SP1Clean.Soundness.LoadByteStatic.assembly_raw_count',
        'SP1Clean.Soundness.LoadByteStatic.assembly_balanced',
        'SP1Clean.Soundness.LoadByteStatic.assembly_acceptance',
    ]
    probe = out / 'Declarations.lean'
    probe.write_text('import SP1Clean.Proofs.Completeness.LoadByteStatic\n\n' +
                     '\n'.join(f'#check {name}\n#print axioms {name}' for name in declarations) + '\n')
    checked = run(['elan', 'run', toolchain, 'lake', 'env', 'lean', str(probe)])
    (out / 'axioms.log').write_text(checked.stdout)
    if (checked.stderr or any(name not in checked.stdout for name in declarations) or
            checked.stdout.count('depends on axioms:') != len(declarations) or
            any(token in checked.stdout for token in ['sorryAx', 'native_decide', 'error:', 'warning:'])):
        raise RuntimeError('Incomplete declaration/axiom report or unexpected trust/Lean diagnostic')
    provenance['sourceStatusAfter'] = git('status', '--porcelain', '--untracked-files=normal')
    provenance['sourceDigestAfter'] = source_digest()
    provenance['revisionAfter'] = git('rev-parse', 'HEAD')
    if (provenance['sourceStatusAfter'] != provenance['sourceStatusBefore'] or
            provenance['sourceDigestAfter'] != provenance['sourceDigestBefore'] or
            provenance['revisionAfter'] != provenance['revision']):
        raise RuntimeError('Source status changed while running; rerun on a stable checkout')
    provenance['status'] = 'passed'
    print(f"PASS {len(expected)} LoadByte cases; results and literal axiom reports in {out}")
except Exception as error:
    provenance['status'] = 'failed'
    provenance['error'] = str(error)
    raise
finally:
    (out / 'provenance.json').write_text(json.dumps(provenance, indent=2) + '\n')
PY
