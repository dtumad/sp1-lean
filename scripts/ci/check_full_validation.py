#!/usr/bin/env python3
"""Require the complete CI dependency graph, including matrix job results."""

import json
import os


REQUIRED = {"guards", "build", "export-generate", "export-verify", "export-rust"}


def validate(jobs):
    if set(jobs) != REQUIRED:
        raise ValueError(f"Incomplete validation graph: {set(jobs) ^ REQUIRED}")
    failed = {name: job.get("result") for name, job in jobs.items()
              if job.get("result") != "success"}
    if failed:
        raise ValueError(f"Required validation did not pass: {failed}")
    if jobs["build"].get("outputs", {}).get("full-build") != "true":
        raise ValueError("Core-only validation cannot satisfy build-full")


if __name__ == "__main__":
    validate(json.loads(os.environ["REQUIRED_JOBS"]))
    print("PASS: full Lean, export and Rust validation")
