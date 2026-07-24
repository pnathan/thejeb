#!/usr/bin/env bash
#
# Run the general chunking extraction pipeline on a corpus, then score the
# resulting frames.json with the verified Lean `tides` STE exe.
#
# Example:
#   scripts/corpus/run.sh \
#     --corpus sources/federalist --out build/federalist \
#     --topic "the design and defense of the proposed U.S. Constitution" \
#     --jobs 6
#
# All flags are forwarded to extract_corpus.py; --out is also used to locate
# frames.json for the Lean step. Pass --no-lean to stop after extraction.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

OUT=""; NO_LEAN=0; PASS=()
while [ $# -gt 0 ]; do
  case "$1" in
    --out) OUT="$2"; PASS+=("$1" "$2"); shift 2 ;;
    --no-lean) NO_LEAN=1; shift ;;
    *) PASS+=("$1"); shift ;;
  esac
done
[ -n "$OUT" ] || { echo "need --out DIR" >&2; exit 2; }

python3 "$SCRIPT_DIR/extract_corpus.py" "${PASS[@]}"

if [ "$NO_LEAN" -eq 1 ]; then exit 0; fi

# Absolute path so the exe (cwd = lean/) finds it.
case "$OUT" in /*) ABS="$OUT" ;; *) ABS="$ROOT/$OUT" ;; esac
printf '\n== Lean — verified STE over %s ==\n' "$ABS/frames.json"
cd "$ROOT/lean"
lake build tides >/dev/null
lake exe tides "$ABS/frames.json"
