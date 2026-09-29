#!/usr/bin/env bash
# Reproduce the assembled BEQ witness and retain original command/theorem output as CI artifacts.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
if [[ $# != 0 ]]; then
  echo 'usage: scripts/check_branch_ensemble.sh' >&2
  exit 2
fi
python3 - <<'PY'
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys

out = Path('.lake/build/branch-ensemble')
out.mkdir(parents=True, exist_ok=True)
# Never let an earlier successful output stand in for a crashed or incomplete current run.
for name in ('results.json', 'axioms.log', 'runner.stdout.log', 'commands.log', 'build.log'):
    (out / name).unlink(missing_ok=True)
toolchain = Path('lean-toolchain').read_text().strip()
env = dict(os.environ)
env.setdefault('LEAN_NUM_THREADS', '2')

def run(command, log=None):
    with (out / 'commands.log').open('a') as stream:
        stream.write('$ ' + shlex.join(command) + '\n')
    result = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, env=env)
    with (out / 'commands.log').open('a') as stream:
        stream.write(result.stdout)
        stream.write(result.stderr)
        stream.write(f'\n[exit {result.returncode}]\n')
    if log:
        (out / log).write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError(f'{shlex.join(command)} exited {result.returncode}; see {out}/commands.log')
    return result

def git(*args):
    return run(['git', *args]).stdout.strip()

def source_digest():
    paths = subprocess.check_output(['git', 'ls-files', '--cached', '--others',
                                     '--exclude-standard', '-z']).split(b'\0')
    digest = hashlib.sha256()
    for name in sorted(set(paths) - {b''}):
        path = Path(os.fsdecode(name))
        digest.update(name + b'\0')
        if path.is_symlink():
            digest.update(b'link\0' + os.fsencode(os.readlink(path)))
        elif path.is_file():
            digest.update(str(path.stat().st_mode & 0o777).encode() + b'\0' + path.read_bytes())
        else:
            digest.update(b'<missing>')
        digest.update(b'\0')
    return digest.hexdigest()

provenance = {'status': 'started', 'startedUtc': datetime.now(timezone.utc).isoformat(),
              'toolchain': toolchain, 'leanNumThreads': env['LEAN_NUM_THREADS']}
def save_provenance():
    (out / 'provenance.json').write_text(json.dumps(provenance, indent=2) + '\n')
save_provenance()
try:
    provenance.update({
        'revision': git('rev-parse', 'HEAD'), 'tree': git('rev-parse', 'HEAD^{tree}'),
        'dirty': bool(git('status', '--porcelain', '--untracked-files=normal')),
        'workingSourceSha256': source_digest(),
        'trackedDiffSha256': hashlib.sha256(run(['git', 'diff', 'HEAD']).stdout.encode()).hexdigest(),
        'projectCachePresentBeforeBuild': Path('.lake/build/lib/lean').is_dir(),
        'fixtureOleanPresentBeforeBuild': Path('.lake/build/lib/lean/SP1CleanTest/Alignment/Audit/BranchEnsembleRoundTrip.olean').is_file(),
        'cacheNote': 'Uses prepared dependencies and available project oleans; no cold-build timing claim.',
        'ci': {key: os.environ.get(key) for key in
               ('GITHUB_SHA', 'GITHUB_HEAD_REF', 'GITHUB_BASE_REF', 'GITHUB_RUN_ID',
                'GITHUB_RUN_ATTEMPT', 'GITHUB_REPOSITORY', 'SP1_BRANCH_PR_HEAD')}})
    manifest = json.loads(Path('lake-manifest.json').read_text())
    provenance['dependencies'] = [{'name': p['name'], 'url': p.get('url'), 'revision': p['rev']}
                                  for p in manifest['packages']]
    save_provenance()
    # The runner installs nothing. Fail before Lake could fetch a missing or moved dependency.
    run(['elan', 'run', toolchain, 'lean', '--version'])
    run(['scripts/check_pins.sh'])
    for package in manifest['packages']:
        directory = Path(manifest['packagesDir']) / package['name']
        if package['type'] != 'git' or not (directory / '.git').exists():
            raise RuntimeError(f'Missing pinned {package["name"]}; prepare dependencies as in docs/branch-ensemble.md')
        if git('-C', str(directory), 'rev-parse', 'HEAD') != package['rev']:
            raise RuntimeError(f'{package["name"]}: checkout differs from the resolved pin')
        if git('-C', str(directory), 'status', '--porcelain', '--untracked-files=no'):
            raise RuntimeError(f'{package["name"]}: tracked dependency edits')
    run(['elan', 'run', toolchain, 'lake', '--no-cache', 'build', '--wfail', '--iofail',
         'SP1CleanTest.Alignment.Audit.BranchEnsembleRoundTrip'], 'build.log')
    env['SP1_BRANCH_REVISION'] = provenance['revision']
    env['SP1_BRANCH_STATUS'] = 'dirty' if provenance['dirty'] else 'clean'
    evaluated = run(['elan', 'run', toolchain, 'lake', 'env', 'lean',
                     'scripts/branchEnsembleExample.lean'], 'runner.stdout.log')
    if evaluated.stderr:
        raise RuntimeError('Unexpected Lean diagnostics in the fixture runner')
    report = json.loads(evaluated.stdout)
    expected_ids = ['active-branch', 'wrong-public-next-pc', 'missing-authentication-row',
                    'duplicate-authentication-row', 'changed-untouched-register', 'empty-identity',
                    'malformed-seed-index', 'malformed-seed-length']
    cases = report['cases']
    if [case['id'] for case in cases] != expected_ids:
        raise RuntimeError('Missing, extra, or reordered regression cases')
    expected_values = [True, False, False, False, False, True, False, False]
    for case, expected in zip(cases, expected_values):
        if type(case['actual']) is not bool or case['actual'] != expected or case['expected'] is not expected:
            raise RuntimeError(f'Regression mismatch: {case}')
    if (report['revision'] != provenance['revision'] or report['dirty'] is not provenance['dirty'] or
        report['assembly'] != 'SP1Clean.Soundness.HostFinalMemory.ensemble' or
        report['instruction'] != 'BEQ x1,x2,+4092' or report['instructionWord'] != 0x7e208ee3 or
        [report[key] for key in ('sourcePc', 'targetPc', 'sourceClock', 'targetClock')] != [65536, 69628, 1, 9] or
        report['tableCount'] != 89 or report['uniqueChannels'] != 22 or
        report['registeredChannelOccurrences'] != 257 or
        report['tableCount'] != len(report['tables']) or
        report['tableRows'] != sum(table['rows'] for table in report['tables']) or
        report['rowsIncludingVerifier'] != report['tableRows'] + 1):
        raise RuntimeError('Fixture metadata or physical-row accounting mismatch')
    # These commands print literal types and their compiled trust dependencies, not paraphrases.
    names = ['Air.Flat.EnsembleExport.checkWitness_iff',
             'Air.Flat.EnsembleWitness.withChannels_balanced',
             'SP1Clean.Audit.BranchEnsemble.source_realizes',
             'SP1Clean.Audit.BranchEnsemble.target_realizes',
             'SP1Clean.Audit.BranchEnsemble.public_endpoints',
             'SP1Clean.Audit.BranchEnsemble.branch_component',
             'SP1Clean.Audit.BranchEnsemble.actual_branch_row',
             'SP1Clean.Audit.BranchEnsemble.accepted',
             'SP1Clean.Audit.BranchEnsemble.statement',
             'SP1Clean.Audit.BranchEnsemble.joined']
    probe = out / 'probe.lean'
    probe.write_text('import SP1CleanTest.Alignment.Audit.BranchEnsembleRoundTrip\n' +
                     '\n'.join(f'#check @{name}\n#print axioms {name}' for name in names) +
                     '\n#eval IO.println "BRANCH_ENSEMBLE_PROBE_COMPLETE"\n')
    inspected = run(['elan', 'run', toolchain, 'lake', 'env', 'lean', str(probe)], 'axioms.log')
    if (inspected.stderr or 'BRANCH_ENSEMBLE_PROBE_COMPLETE' not in inspected.stdout or
        re.search(r'\b(error|warning):|sorryAx', inspected.stdout) or
        any(name not in inspected.stdout for name in names)):
        raise RuntimeError('Incomplete theorem/axiom probe or unexpected trust diagnostic')
    if source_digest() != provenance['workingSourceSha256'] or git('rev-parse', 'HEAD') != provenance['revision']:
        raise RuntimeError('Sources or revision changed during the run; repeat on a stable checkout')
    (out / 'results.json').write_text(evaluated.stdout)
    provenance['status'] = 'passed'
    save_provenance()
    print(evaluated.stdout, end='')
    print(f'PASS assembled branch; original logs and provenance: {out}')
except Exception as error:
    provenance.update({'status': 'failed', 'failure': str(error)})
    save_provenance()
    print(str(error), file=sys.stderr)
    sys.exit(1)
PY
