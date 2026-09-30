#!/usr/bin/env bash
# Regenerate the whole-ensemble fixture and compare every output. A fresh workspace-local
# directory ensures Lean's known exit-zero stack-overflow behavior cannot reuse stale files.
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .lake/capstone-scratch
scratch=$(mktemp -d "$PWD/.lake/capstone-scratch/ensemble-export.XXXXXX")
ENSEMBLE_EXPORT_OUT="$scratch" lake env lean scripts/ensembleExportFixture.lean
for file in lookup.instance.json lookup.valid.json lookup.forged.json; do
  cmp "export/ensemble/$file" "$scratch/$file"
done
echo "PASS: whole-ensemble export fixture is byte-identical"
