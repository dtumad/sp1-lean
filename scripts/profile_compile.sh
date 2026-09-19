#!/usr/bin/env bash
#
# profile_compile.sh — rank every hand-written module by wall-clock elaboration time.
#
# Method: after one warm `lake build` (so every dependency is a cached .olean), run
#   lake env lean -Dprofiler=true -Dprofiler.threshold=50 [linter flags] <file>
# on each module. Because deps load from cache, this isolates that file's own elaboration
# cost. We time it with /usr/bin/time -p and capture the profiler breakdown to a per-file log,
# then scripts/profile_aggregate.py turns the logs into a ranking plus a per-category and
# per-pillar cost split (import, elaboration, simp, tactic execution, type checking, typeclass
# inference, compilation, linting, ...).
#
# Caveats baked in:
#   - `lake env lean` exits 0 even on a stack overflow, so we record exit codes explicitly and
#     surface any nonzero ones — a silent failure must not be misread as "fast".
#   - Runs sequentially: clean wall-clock numbers, and respects the repo's build-concurrency cap.
#   - A warm full build must precede the sweep, or early files pay to build their deps.
#   - `lake env` only sets environment variables; it applies neither a library's `moreLeanArgs`
#     nor the package's `moreLeanArgs`/`[leanOptions]`. The sweep therefore passes the package
#     flags (`--tstack=400000 -DsynthInstance.maxHeartbeats=1000000`) and the eight style-linter
#     flags from lakefile.toml itself (the linters are skipped for the generated
#     `SP1Clean/Extracted/` modules, which carry `set_option linter.all false` and are built
#     without them). Keep these lists in sync with lakefile.toml.
#   - The Lake environment is captured once (`lake env` with no command) and `lean` is invoked
#     directly, so per-module wall time is Lean alone, without ~1 s of Lake startup per file.
#   - Numbers are per-module wall time of one `lean` process. Lean elaborates proof bodies
#     asynchronously, so the profiler's `blocked (unaccounted)` category is time the main thread
#     waited for those tasks; read it together with `simp`/`tactic execution`/`type checking`.
#     For a real parallel build's per-module times, feed its log to
#     `scripts/profile_aggregate.py --lake-log <log>` instead.
#
# Usage:
#   scripts/profile_compile.sh [PATH_PREFIX]
#     PATH_PREFIX  optional repo-relative path prefix to restrict the sweep
#                  (e.g. SP1Clean/Math/ or ToClean/).
#
# Env:
#   TREES=…        space-separated source trees to sweep (default: "SP1Clean ToClean ToMathlib").
#                  Add SP1CleanTest to include the test library (its warm build is `lake build
#                  SP1CleanTest`, the native_decide battery).
#   SKIP_BUILD=1   skip the warm build (use when the cache is already warm).
#   EXCLUDE_RE=…   optional grep -E pattern of module paths to skip.
#   OUTDIR=…       output directory (default .lake/profile, gitignored).
#   TOP=…          rows in the ranking tables (default 50).
#
# Outputs (under $OUTDIR):
#   <module>.log         full -Dprofiler stdout+stderr for each module
#   summary.tsv          seconds<TAB>exit<TAB>module, sorted slowest-first (the offender ranking)
#   summary.md           the ranking as a markdown table with a totals/failures footer
#   measurements.jsonl   one JSON-Lines record per module (archival)
#   profile.md           ranking + category totals + per-pillar split (from profile_aggregate.py)
#   profile.json         the same data, machine-readable

set -u
set -o pipefail

cd "$(dirname "$0")/.." || exit 1
ROOT="$(pwd)"
OUTDIR="${OUTDIR:-$ROOT/.lake/profile}"
PREFIX="${1:-}"
TREES="${TREES:-SP1Clean ToClean ToMathlib}"
TOP="${TOP:-50}"

# Package-level lean args (lakefile.toml `moreLeanArgs` + `[leanOptions]`), applied to every module.
PACKAGE_FLAGS=(--tstack=400000 -DsynthInstance.maxHeartbeats=1000000)
# Per-library style linters (lakefile.toml, the eight-flag block), applied to hand-written modules.
LINTER_FLAGS=(
  -Dlinter.style.lambdaSyntax=true -Dlinter.style.dollarSyntax=true
  -Dlinter.style.refine=true -Dlinter.style.cases=true
  -Dlinter.style.induction=true -Dlinter.style.admit=true
  -Dlinter.oldObtain=true -Dlinter.style.cdot=true
)

mkdir -p "$OUTDIR"
: > "$OUTDIR/summary.tsv"
: > "$OUTDIR/measurements.jsonl"

# 1. Warm the olean cache. Abort the sweep if the build is broken — profiling a non-building
#    tree measures error-recovery, not steady-state elaboration.
if [ "${SKIP_BUILD:-0}" != "1" ]; then
  echo ">>> Warming cache: lake build"
  pkill -f "lake build" 2>/dev/null
  pkill -f "lake env lean" 2>/dev/null
  if ! lake build; then
    echo "!!! warm build failed — fix the build before profiling. Aborting." >&2
    exit 1
  fi
  case " $TREES " in
    *" SP1CleanTest "*)
      echo ">>> Warming cache: lake build SP1CleanTest"
      if ! lake build SP1CleanTest; then
        echo "!!! warm test build failed — fix the build before profiling. Aborting." >&2
        exit 1
      fi ;;
  esac
else
  echo ">>> SKIP_BUILD=1: assuming cache is warm"
fi

# 1b. Capture the Lake environment once (LEAN_PATH etc.) so each module runs `lean` directly.
while IFS= read -r line; do
  case "$line" in [A-Za-z_]*=*) export "$line" ;; esac
done < <(lake env)
LEAN_BIN="${LEAN:-lean}"
command -v "$LEAN_BIN" >/dev/null 2>&1 || LEAN_BIN="$(lake env which lean 2>/dev/null || echo lean)"
echo ">>> lean: $("$LEAN_BIN" --version 2>/dev/null | head -1)"

# 2. Enumerate modules (deterministic order), optionally scoped by path prefix.
#    bash 3.2 has no `mapfile`, so stream from a temp list and count up front.
LISTFILE="$(mktemp)"
for tree in $TREES; do
  [ -d "$tree" ] && find "$tree" -name '*.lean'
done | sort > "$LISTFILE"
if [ -n "$PREFIX" ]; then
  grep "^$PREFIX" "$LISTFILE" > "$LISTFILE.f"; mv "$LISTFILE.f" "$LISTFILE"
fi
if [ -n "${EXCLUDE_RE:-}" ]; then
  grep -Ev "$EXCLUDE_RE" "$LISTFILE" > "$LISTFILE.f"; mv "$LISTFILE.f" "$LISTFILE"
fi
TOTAL="$(wc -l < "$LISTFILE" | tr -d ' ')"

echo ">>> Profiling ${TOTAL} modules (trees='${TREES}' prefix='${PREFIX}') -> $OUTDIR"
count=0
while IFS= read -r f; do
  count=$((count + 1))

  # dotted module name, e.g. SP1Clean/Math/Word.lean -> SP1Clean.Math.Word
  module="${f%.lean}"
  module="${module//\//.}"
  log="$OUTDIR/${module}.log"
  timefile="$(mktemp)"

  # Generated modules are built without the style linters (lakefile.toml `SP1Extracted`).
  case "$f" in
    SP1Clean/Extracted/*) flags=() ;;
    *) flags=("${LINTER_FLAGS[@]}") ;;
  esac

  printf '[%3d/%3d] %s ... ' "$count" "$TOTAL" "$module"

  # 3. Time the isolated elaboration. lean runs inside `sh -c` so ITS stdout+stderr (incl. the
  #    profiler breakdown) go to $log, while /usr/bin/time -p's own `real <sec>` line stays on
  #    the outer stderr -> $timefile. time -p exits with the wrapped command's status, so rc is
  #    lean's exit code. (Redirecting lean directly under time would capture time's output too.)
  /usr/bin/time -p sh -c \
    'log="$1"; lean="$2"; shift 2; "$lean" -Dprofiler=true -Dprofiler.threshold=50 "$@" > "$log" 2>&1' \
    _ "$log" "$LEAN_BIN" "${PACKAGE_FLAGS[@]}" "${flags[@]}" "$f" 2> "$timefile"
  rc=$?

  secs="$(awk '/^real/ {print $2}' "$timefile")"
  rm -f "$timefile"
  [ -z "$secs" ] && secs="0"

  printf '%ss (exit %d)\n' "$secs" "$rc"
  printf '%s\t%s\t%s\n' "$secs" "$rc" "$module" >> "$OUTDIR/summary.tsv"
  printf '{"metric": "compile//%s", "value": %s, "unit": "s", "exit": %d}\n' \
    "$module" "$secs" "$rc" >> "$OUTDIR/measurements.jsonl"
done < "$LISTFILE"
rm -f "$LISTFILE"

# 4. Sort slowest-first; that sorted file IS the canonical offender ranking.
sort -t$'\t' -k1,1 -rn "$OUTDIR/summary.tsv" -o "$OUTDIR/summary.tsv"

# 5. Render a markdown table + a totals/failures footer.
{
  echo "# Compile-time profile (wall-clock elaboration, isolated per module)"
  echo
  echo "| Rank | Seconds | Exit | Module |"
  echo "| ---: | ---: | ---: | --- |"
  awk -F'\t' '{ printf "| %d | %.2f | %d | \x60%s\x60 |\n", NR, $1, $2, $3 }' "$OUTDIR/summary.tsv"
  echo
  awk -F'\t' '
    { total += $1; n++; if ($2 != 0) fails[$2"\t"$3]=1 }
    END {
      printf "**Total:** %.1fs across %d modules (sequential; no parallelism/kernel phase).\n\n", total, n
      nf = 0; for (k in fails) nf++
      if (nf > 0) {
        printf "**%d module(s) exited nonzero** (silent under `lake env lean` — investigate):\n\n", nf
        for (k in fails) { split(k, a, "\t"); printf "- `%s` (exit %s)\n", a[2], a[1] }
      } else {
        print "All modules exited 0."
      }
    }' "$OUTDIR/summary.tsv"
} > "$OUTDIR/summary.md"

# 6. Category and per-pillar split from the profiler logs.
python3 "$ROOT/scripts/profile_aggregate.py" --profile-dir "$OUTDIR" --top "$TOP"

echo
echo ">>> Done. Ranking: $OUTDIR/summary.tsv  |  Split: $OUTDIR/profile.md  |  Logs: $OUTDIR/*.log"
echo ">>> Top 15:"
head -15 "$OUTDIR/summary.tsv" | awk -F'\t' '{ printf "  %6.2fs  (exit %s)  %s\n", $1, $2, $3 }'
