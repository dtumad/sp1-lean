#!/usr/bin/env bash
# End-to-end runner regression: evaluate real cases twice, then deliberately fail one expectation.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
python3 - <<'PY'
import json
from pathlib import Path
import os
import subprocess
import tempfile

runner = Path('scripts/run_talk_examples.sh').resolve()
def require(condition, message):
    if not condition:
        raise RuntimeError(message)

with tempfile.TemporaryDirectory(prefix='sp1-talk-check-') as outside:
    first = subprocess.run([str(runner), '--json'], check=True, text=True, stdout=subprocess.PIPE)
    second = subprocess.run([str(runner), '--json'], cwd=outside, check=True,
                            text=True, stdout=subprocess.PIPE)
    require(first.stdout == second.stdout, 'unchanged runs must produce identical JSON')
    require(len(json.loads(first.stdout)['cases']) == 9, 'all nine cases must run')
    wrong = subprocess.run([str(runner), '--json'], env={**os.environ, 'SP1_TALK_INVERT_EXPECTATION': '1'},
                           text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    require(wrong.returncode == 1, f'mismatching expectation returned {wrong.returncode}')
    require(not wrong.stdout, 'failed output must not be presented as a successful report')
    require('Fixture expectation mismatch.' in wrong.stderr, 'actual mismatch must be reported')
    unknown = subprocess.run([str(runner), '--unknown'], text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    require(unknown.returncode == 2 and 'usage:' in unknown.stderr, 'unknown option must fail')

    # Fault-inject only the subprocess boundary after measuring actual fixture results above.
    # This covers Lean's known zero-exit stack-overflow trap, even after complete JSON output.
    fake_bin = Path(outside) / 'bin'
    fake_bin.mkdir()
    payload = Path(outside) / 'payload.json'
    payload.write_text(first.stdout)
    fake_elan = fake_bin / 'elan'
    fake_elan.write_text('''#!/usr/bin/env python3
import json, os, sys
if 'env' in sys.argv:
    report = json.load(open(os.environ['TALK_CHECK_PAYLOAD']))
    report['revision'] = os.environ['SP1_TALK_REVISION']
    report['dirty'] = os.environ['SP1_TALK_STATUS'] == 'dirty'
    fault = os.environ['TALK_CHECK_FAULT']
    if fault == 'mismatch':
        report['cases'][0]['actual'] = not report['cases'][0]['expected']
    print(json.dumps(report))
    if fault == 'stderr':
        print('error: stack overflow', file=sys.stderr)
    if fault == 'stdout':
        print('error: stack overflow')
''')
    fake_elan.chmod(0o755)
    for fault in ['stderr', 'stdout', 'mismatch']:
        failed = subprocess.run([str(runner), '--json'], text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                env={**os.environ, 'PATH': str(fake_bin) + os.pathsep + os.environ['PATH'],
                                     'TALK_CHECK_PAYLOAD': str(payload), 'TALK_CHECK_FAULT': fault,
                                     'PYTHONOPTIMIZE': '1'})
        require(failed.returncode == 1 and not failed.stdout, f'zero-exit {fault} must fail closed')
print('PASS nine real cases, deterministic JSON, outside-directory invocation, mismatch exit, unknown option, zero-exit faults')
PY
