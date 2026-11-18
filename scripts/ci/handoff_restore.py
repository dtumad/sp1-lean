#!/usr/bin/env python3
"""handoff_restore.py — restore a completed pull-request build instead of rebuilding it.

Every successful pull-request run uploads its packed `.lake` tree as `lake-full-build-<head sha>`
(.github/workflows/lean_action_ci.yml, "Hand off the completed PR build"). Two later runs can start
from it:

  main   a push to `main` that merges a PR: the merged head is `HEAD^2`. The artifact is consumed
         once and deleted.
  pr     a stacked pull request, whose base is another PR's branch: its merge ref is built on that
         branch's head, so `HEAD^1` is the parent PR's head. The lineage cache (`cache_pick.py`)
         can only offer `main`, which may predate the whole stack; the parent's hand-off differs
         from this tree only by this PR's own commits. The artifact is kept for the parent's own
         merge. If the parent's run for that head is still queued or running, wait for it (bounded
         by `--timeout`) rather than rebuild everything in parallel.

Prints `restored=true` (for `$GITHUB_OUTPUT`) when it extracted a build; otherwise prints nothing and
the job falls back to the lineage cache. Never fails the job: every error degrades to a fallback.

Usage:
  scripts/ci/handoff_restore.py --mode main --repo owner/name
  scripts/ci/handoff_restore.py --mode pr --repo owner/name --base-ref <branch> [--timeout 180]

The default wait covers a stack pushed at once (each level waits for the one below it) while a
fallback cold build still fits the build job's 350-minute limit.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time

ARTIFACT_PREFIX = "lake-full-build-"
WORKFLOW = "lean_action_ci.yml"
WAITING = ("queued", "in_progress", "waiting", "pending", "requested")


def wanted_sha(mode: str, base_ref: str | None, parents: list[str]) -> str | None:
    """The head whose hand-off this run can use: `HEAD^2` of a merge on main, or `HEAD^1` of a
    stacked PR's merge ref. `parents` lists HEAD's parents in order. Pure."""
    if mode == "main":
        return parents[1] if len(parents) > 1 else None
    if mode == "pr" and base_ref and base_ref != "main" and parents:
        return parents[0]
    return None


def decide(artifacts: list[dict], runs: list[dict]) -> tuple[str, int | None]:
    """What to do now: ("restore", artifact id), ("wait", None) while a run for the head is still
    going, or ("fallback", None). Pure."""
    live = [a for a in artifacts if not a.get("expired")]
    if live:
        return "restore", max(live, key=lambda a: a.get("created_at", ""))["id"]
    if any(r.get("status") in WAITING for r in runs):
        return "wait", None
    return "fallback", None


def gh(*args: str) -> str:
    return subprocess.run(["gh", *args], check=True, capture_output=True, text=True).stdout


def lookup(repo: str, sha: str) -> tuple[list[dict], list[dict]]:
    artifacts = json.loads(gh("api", f"repos/{repo}/actions/artifacts?name={ARTIFACT_PREFIX}{sha}&per_page=5"))
    runs = json.loads(gh("api", f"repos/{repo}/actions/workflows/{WORKFLOW}/runs?head_sha={sha}&per_page=20"))
    return artifacts.get("artifacts", []), runs.get("workflow_runs", [])


def restore(repo: str, artifact_id: int) -> None:
    with open("handoff.zip", "wb") as out:
        subprocess.run(["gh", "api", f"repos/{repo}/actions/artifacts/{artifact_id}/zip"], check=True, stdout=out)
    subprocess.run(["unzip", "-q", "handoff.zip"], check=True)
    subprocess.run(["tar", "--zstd", "-xf", "lake-build.tar.zst"], check=True)
    subprocess.run(["rm", "-f", "handoff.zip", "lake-build.tar.zst"], check=True)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--mode", choices=["main", "pr"], required=True)
    ap.add_argument("--repo", required=True)
    ap.add_argument("--base-ref")
    ap.add_argument("--timeout", type=float, default=180, help="minutes to wait for a running parent")
    ap.add_argument("--poll", type=float, default=60, help="seconds between polls")
    args = ap.parse_args()

    parents = subprocess.run(["git", "rev-list", "--parents", "-n", "1", "HEAD"], check=True,
                             capture_output=True, text=True).stdout.split()[1:]
    sha = wanted_sha(args.mode, args.base_ref, parents)
    if not sha:
        print("no hand-off applies; lineage restore", file=sys.stderr)
        return
    deadline = time.monotonic() + args.timeout * 60
    try:
        while True:
            artifacts, runs = lookup(args.repo, sha)
            action, artifact_id = decide(artifacts, runs if args.mode == "pr" else [])
            if action == "restore":
                restore(args.repo, artifact_id)
                if args.mode == "main":
                    subprocess.run(["gh", "api", "-X", "DELETE", f"repos/{args.repo}/actions/artifacts/{artifact_id}"],
                                   check=False)
                print(f"restored the hand-off of {sha}", file=sys.stderr)
                print("restored=true")
                return
            if action == "wait" and time.monotonic() < deadline:
                print(f"the run for {sha} is still going; waiting", file=sys.stderr)
                time.sleep(args.poll)
                continue
            print(f"no hand-off for {sha}; lineage restore", file=sys.stderr)
            return
    except (subprocess.CalledProcessError, json.JSONDecodeError, OSError) as err:
        print(f"hand-off unavailable ({err}); lineage restore", file=sys.stderr)


if __name__ == "__main__":
    main()
