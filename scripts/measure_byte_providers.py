#!/usr/bin/env python3
"""Measure the existing Rust comparison test with isolated per-layout peak RSS.

Build unified_byte_export with check_ensemble_export.sh first. Each subprocess performs
one warmup and three sequential samples using the Plonky3 benchmark FRI configuration.
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
    cases = [(case["name"], False) for case in reference["benchmarks"]]
    cases += [(f"{kind}-{n}", True) for n in [1024, 16384, 65536]
              for kind in ["mixed-distinct", "hot"]]
    for name, large in cases:
        for layout in ["baseline", "candidate", "fixed"]:
            log = out / f"measure-{name}-{layout}.log"
            env = dict(os.environ, BYTE_BENCH_CASE=name, BYTE_BENCH_LAYOUT=layout,
                       RAYON_NUM_THREADS="2")
            test = "large_provider_layout_measurements" if large else "provider_layout_measurements"
            command = [str(args.binary.resolve()), "--exact", test,
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
            exported_layout = "routed" if layout == "baseline" else layout
            source = (f"byte_large_{exported_layout}_{name.rsplit('-', 1)[1]}.rs"
                      if large else f"byte_{exported_layout}_{name}.rs")
            measurements.append({
                "name": name, "layout": layout, "samples": samples,
                "peakRssBytes": usage.ru_maxrss * (1 if platform.system() == "Darwin" else 1024),
                "exportBytes": (out / source).stat().st_size,
            })
            print(f"Measured {name}/{layout}", flush=True)
    result = {"platform": platform.platform(), "threads": 2, "warmups": 1,
              "samplesPerLayout": 3,
              "friProfile": "Plonky3 create_benchmark_fri_params",
              "proveScope": "includes preprocessing on every invocation; no reusable-key API",
              "proofSizeEncoding": "JSON bytes, not a canonical binary protocol encoding",
              "largeBoundary": "common runtime request table; public binding tested by small fixtures",
              "peakRssScope": "one layout process including warmup",
              "candidateMetrics": reference["candidateMetrics"],
              "baselineMetrics": reference["baselineMetrics"], "measurements": measurements}
    (out / "byte-provider-measurements.json").write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
