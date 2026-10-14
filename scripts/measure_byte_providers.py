#!/usr/bin/env python3
"""Measure the existing Rust comparison test with isolated per-layout peak RSS.

Build unified_byte_export with check_ensemble_export.sh first. Each subprocess performs
one warmup and three sequential samples using the shared backend test configuration.
All output, including generated sources, belongs in the ignored export directory.
"""

import argparse
import json
import os
from pathlib import Path
import platform
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifacts", type=Path, required=True)
    parser.add_argument("--binary", type=Path, required=True)
    args = parser.parse_args()
    out = args.artifacts.resolve()
    reference = json.loads((out / "unified_byte.reference.json").read_text())
    measurements = []
    for case in reference["benchmarks"]:
        for layout in ["baseline", "candidate"]:
            name = case["name"]
            log = out / f"measure-{name}-{layout}.log"
            env = dict(os.environ, BYTE_BENCH_CASE=name, BYTE_BENCH_LAYOUT=layout,
                       RAYON_NUM_THREADS="2")
            command = [str(args.binary.resolve()), "--exact", "provider_layout_measurements",
                       "--nocapture", "--test-threads=1"]
            with log.open("w") as output:
                process = subprocess.Popen(command, env=env, stdout=output, stderr=subprocess.STDOUT)
                _, status, usage = os.wait4(process.pid, 0)
                process.returncode = os.waitstatus_to_exitcode(status)
            text = log.read_text()
            samples = [json.loads(line.split("BYTE_MEASUREMENT ", 1)[1])
                       for line in text.splitlines() if "BYTE_MEASUREMENT " in line]
            if (process.returncode or len(samples) != 3 or
                    "test result: ok. 1 passed; 0 failed;" not in text):
                raise SystemExit(f"Incomplete measurement: {log}")
            if any(sample["name"] != name or sample["layout"] != layout for sample in samples):
                raise SystemExit(f"Wrong measurement selection: {log}")
            measurements.append({
                "name": name, "layout": layout, "samples": samples,
                "peakRssBytes": usage.ru_maxrss * (1 if platform.system() == "Darwin" else 1024),
                "exportBytes": (out / f"byte_{layout}_{name}.rs").stat().st_size,
            })
            print(f"Measured {name}/{layout}", flush=True)
    result = {"platform": platform.platform(), "threads": 2, "warmups": 1,
              "samplesPerLayout": 3, "peakRssScope": "one layout process including warmup",
              "candidateMetrics": reference["candidateMetrics"],
              "baselineMetrics": reference["baselineMetrics"], "measurements": measurements}
    (out / "byte-provider-measurements.json").write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
