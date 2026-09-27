import json
import os
from pathlib import Path
import subprocess
import time

env = dict(os.environ, LEAN_NUM_THREADS="2")
results = json.loads(Path(".lake/branch-validation.json").read_text())
for name, command, out, err in [
    ("driver", ["lake", "env", "lean", "scripts/branchCompilerExample.lean"],
     ".lake/branch-output.json", ".lake/branch-driver.log"),
    ("theorems-and-axioms", ["lake", "env", "lean", ".lake/branch-evidence-probe.lean"],
     ".lake/branch-theorems-and-axioms.txt", ".lake/branch-probe-stderr.log"),
]:
    if any(item["name"] == name and item["exitCode"] == 0 for item in results):
        continue
    start = time.monotonic()
    with Path(out).open("w") as stdout, Path(err).open("w") as stderr:
        result = subprocess.run(command, stdout=stdout, stderr=stderr, env=env)
    if result.returncode or Path(err).read_text():
        raise SystemExit(f"{name} failed or produced stderr: {result.returncode}")
    text = Path(out).read_text()
    if name == "driver":
        report = json.loads(text)
        expected = dict(pc=65536, clock=1, opcode=40, rs1=1, rs2=2,
                        rs1Value=0, rs2Value=0, immediate=4092, taken=True,
                        nextPc=69628, previousRs1Clock=0, previousRs2Clock=0)
        assert report["event"] == expected, report
        for key, value in dict(instructionWord=0x7e208ee3, compiled=True, rowCount=1,
                               rowIsReal=1, rowNextPc=69628, flatConstraintCheck=True).items():
            assert report[key] == value, (key, report)
        assert report["rowWidth"] > 0 and report["constraintCount"] > 0
    elif name == "theorems-and-axioms":
        assert "sorryAx" not in text and "error:" not in text and "warning:" not in text
        assert "joined (policy" in text and "depends on axioms" in text
    results.append(dict(name=name, command=command, exitCode=result.returncode,
                        seconds=round(time.monotonic() - start, 2), stderrEmpty=True))
    Path(".lake/branch-validation.json").write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results[-1]), flush=True)
print("Parsed driver JSON and checked every intended concrete field; axiom probe clean.")
