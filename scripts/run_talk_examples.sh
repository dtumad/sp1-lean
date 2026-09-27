#!/usr/bin/env bash
# Actual assembled AIR fixture checks. Build messages go to stderr; --json is machine-readable.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

mode=--text
if [[ $# == 1 && $1 == --json ]]; then
  mode=--json
elif [[ $# != 0 ]]; then
  echo 'usage: scripts/run_talk_examples.sh [--json]' >&2
  exit 2
fi

for prerequisite in git python3 elan; do
  if ! command -v "$prerequisite" >/dev/null 2>&1; then
    echo "Missing $prerequisite. Install the prerequisites in docs/talk-examples.md, then retry." >&2
    exit 2
  fi
done
toolchain=$(cat lean-toolchain)
# Unlike elan's lean/lake proxies, `elan run` without --install will not install a toolchain.
if ! elan run "$toolchain" lean --version >/dev/null 2>&1; then
  echo "Missing installed toolchain $toolchain. Run: elan toolchain install '$toolchain'" >&2
  exit 2
fi

# Fail before Lake can fetch or change missing/stale packages. Check the resolved graph,
# including inherited dependencies, and reject tracked local edits to dependency sources.
python3 - <<'PY'
import json
from pathlib import Path
import re
import subprocess
import sys

manifest = json.loads(Path('lake-manifest.json').read_text())
errors = []
by_name = {package['name']: package for package in manifest['packages']}
for block in re.split(r'\[\[require\]\]', Path('lakefile.toml').read_text())[1:]:
    body = re.split(r'\n\[\[', block)[0]
    name = re.search(r'^name = "([^"]+)"', body, re.M)
    revision = re.search(r'^rev = "([^"]+)"', body, re.M)
    if name and revision:
        package = by_name.get(name[1], {})
        if revision[1] != package.get('inputRev') and revision[1] != package.get('rev'):
            errors.append(f"{name[1]}: lakefile and resolved manifest disagree")
for package in manifest['packages']:
    directory = Path(manifest['packagesDir']) / package['name']
    if package['type'] != 'git' or not (directory / '.git').exists():
        errors.append(f"{package['name']}: missing pinned git checkout at {directory}")
        continue
    revision = subprocess.check_output(['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True).strip()
    if revision != package['rev']:
        errors.append(f"{package['name']}: expected {package['rev']}, found {revision}")
    dirty = subprocess.check_output(['git', '-C', str(directory), 'status', '--porcelain', '--untracked-files=no'], text=True)
    if dirty:
        errors.append(f"{package['name']}: tracked dependency files have local edits")
if errors:
    print('\n'.join(errors), file=sys.stderr)
    print('Prepare the pinned dependencies as described in docs/talk-examples.md; this runner does not download or update them.', file=sys.stderr)
    sys.exit(2)
PY

revision=$(git rev-parse HEAD)
status=clean
if [[ -n $(git status --porcelain --untracked-files=normal) ]]; then status=dirty; fi
elan run "$toolchain" lake --no-cache build --wfail --iofail SP1CleanTest.Alignment.TalkExamples >&2
export SP1_TALK_REVISION="$revision" SP1_TALK_STATUS="$status"
python3 - "$toolchain" "$mode" <<'PY'
import json
import os
import subprocess
import sys

completed = subprocess.run(['elan', 'run', sys.argv[1], 'lake', 'env', 'lean',
                            'scripts/talkExamples.lean'], text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
if completed.returncode:
    print(completed.stderr, file=sys.stderr, end='')
    print(completed.stdout, file=sys.stderr, end='')
    sys.exit(completed.returncode if completed.returncode > 0 else 1)
if completed.stderr:
    print('Unexpected Lean diagnostics; refusing success.', file=sys.stderr)
    print(completed.stderr, file=sys.stderr, end='')
    sys.exit(1)
try:
    report = json.loads(completed.stdout)
    cases = report['cases']
    expected_ids = ['active-add', 'missing-ram-validator', 'duplicate-ram-validator',
                    'wrong-final-record-clock', 'missing-unchanged-register-validators',
                    'changed-untouched-x31', 'changed-untouched-ram',
                    'missing-bank-terminal', 'empty-identity']
    if [case['id'] for case in cases] != expected_ids:
        raise ValueError('missing, extra, or reordered cases')
    if not all(type(case['expected']) is bool and type(case['actual']) is bool and
               case['expected'] == case['actual'] for case in cases):
        raise ValueError('case mismatch')
    if report['revision'] != os.environ['SP1_TALK_REVISION']:
        raise ValueError('revision mismatch')
    if type(report['dirty']) is not bool or report['dirty'] != (os.environ['SP1_TALK_STATUS'] == 'dirty'):
        raise ValueError('working-tree status mismatch')
except (ValueError, KeyError, TypeError):
    print('Incomplete or mismatching fixture output; refusing success.', file=sys.stderr)
    print(completed.stdout, file=sys.stderr, end='')
    sys.exit(1)
if sys.argv[2] == '--json':
    print(completed.stdout, end='')
else:
    print('Executable fixture evidence (not proof certificates)')
    print(f"Revision: {report['revision']} ({'dirty working tree' if report['dirty'] else 'clean'})")
    print(f"Assembly: {report['assembly']} ({report['table_count']} tables)")
    data = report['input']
    values = ', '.join(f"x{r['index']}={r['value']}" for boundary in ['source', 'target']
                       for r in data[boundary]['registers'])
    print(f"{data['instruction']}: {values}")
    print(f"PC {data['source']['pc']} -> {data['target']['pc']}; clock {data['source']['clock']} -> {data['target']['clock']}")
    for case in cases:
        outcome = lambda value: 'accepted' if value else 'rejected'
        print(f"PASS {case['id']}: expected {outcome(case['expected'])}, actual {outcome(case['actual'])}")
PY
