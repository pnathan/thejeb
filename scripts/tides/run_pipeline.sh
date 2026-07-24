#!/usr/bin/env bash
#
# End-to-end local run of the tides STE pipeline:
#
#   corpus (sources/tides/*.txt)
#     -> Haiku  open extraction        (pass 1)  -> pass1.json
#     -> Sonnet schema unification     (pass 2)  -> schema.json
#     -> Haiku  schema-constrained     (pass 3)  -> frames.json
#     -> Lean `tides` exe reads frames.json      -> STE verdict + report
#
# The Claude passes use the committed prompt templates in this directory and
# the `claude` CLI in headless mode (`claude -p`). The Lean step is the `tides`
# executable (lean/TidesExe.lean): it reads frames.json AT RUNTIME and runs the
# verified Ste.FiniteInstance definitions (STE.Consistent, disagreementDegree)
# on the loaded data — the frames are data, never hard-coded.
#
# Usage:
#   scripts/tides/run_pipeline.sh [options]
#     --out DIR        extraction output dir            (default: build/tides)
#     --haiku MODEL    model for passes 1 & 3           (default: haiku)
#     --sonnet MODEL   model for pass 2                 (default: sonnet)
#     --skip-extract   reuse existing frames.json in --out (or committed), no Claude calls
#     --no-lean        stop after extraction; do not run the Lean exe
#     --in-place       write extraction to sources/tides/extraction (overwrites committed)
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

OUT="$ROOT/build/tides"
HAIKU="haiku"
SONNET="sonnet"
SKIP_EXTRACT=0
NO_LEAN=0

while [ $# -gt 0 ]; do
  case "$1" in
    --out)          OUT="$2"; shift 2 ;;
    --haiku)        HAIKU="$2"; shift 2 ;;
    --sonnet)       SONNET="$2"; shift 2 ;;
    --skip-extract) SKIP_EXTRACT=1; shift ;;
    --no-lean)      NO_LEAN=1; shift ;;
    --in-place)     OUT="$ROOT/sources/tides/extraction"; shift ;;
    -h|--help)      sed -n '2,30p' "$0"; exit 0 ;;
    *) echo "unknown option: $1" >&2; exit 2 ;;
  esac
done

mkdir -p "$OUT"
CORPUS_DIR="$ROOT/sources/tides"

say() { printf '\n\033[1m== %s\033[0m\n' "$*"; }

# Concatenate the corpus with per-file headers (provenance comments included).
corpus_blob() {
  local f
  for f in "$CORPUS_DIR"/*.txt; do
    printf '\n### FILE: %s\n' "$(basename "$f")"
    cat "$f"
  done
}

# Extract the first balanced top-level JSON object from mixed model output.
# (Program passed via -c so stdin stays the piped model text; string-aware
# brace counting so braces inside quotes don't throw off the balance.)
JSON_ONLY_PY='
import sys, json
s = sys.stdin.read()
i = s.find("{")
if i < 0:
    sys.exit("no JSON object in model output")
depth = 0; instr = False; esc = False
for j in range(i, len(s)):
    c = s[j]
    if instr:
        if esc: esc = False
        elif c == "\\": esc = True
        elif c == "\"": instr = False
        continue
    if c == "\"": instr = True
    elif c == "{": depth += 1
    elif c == "}":
        depth -= 1
        if depth == 0:
            obj = json.loads(s[i:j+1])
            json.dump(obj, sys.stdout, indent=2)
            sys.exit(0)
sys.exit("unbalanced JSON in model output")
'
json_only() { python3 -c "$JSON_ONLY_PY"; }

# run_claude PROMPT_FILE MODEL  (extra context read from stdin) -> JSON on stdout
# Retries on transient API errors / empty results.
run_claude() {
  local prompt_file="$1" model="$2"
  local prompt env result attempt
  prompt="$( { cat "$prompt_file"; printf '\n\n----- CONTEXT BELOW -----\n'; cat; } )"
  for attempt in 1 2 3; do
    env="$(printf '%s' "$prompt" | claude -p --model "$model" --output-format json 2>/dev/null || true)"
    if [ "$(printf '%s' "$env" | jq -r '.is_error // false' 2>/dev/null)" = "true" ] || [ -z "$env" ]; then
      echo "  [attempt $attempt] claude error: $(printf '%s' "$env" | jq -r '.api_error_status // .result // "empty"' 2>/dev/null | head -c 200)" >&2
      sleep $((attempt * 3)); continue
    fi
    result="$(printf '%s' "$env" | jq -r '.result // empty')"
    if printf '%s' "$result" | json_only 2>/dev/null; then
      return 0
    fi
    echo "  [attempt $attempt] no JSON in result; retrying" >&2
    sleep $((attempt * 3))
  done
  echo "  giving up after 3 attempts on $(basename "$prompt_file")" >&2
  return 1
}

if [ "$SKIP_EXTRACT" -eq 0 ]; then
  command -v claude >/dev/null || { echo "claude CLI not found on PATH" >&2; exit 1; }

  say "Pass 1 — Haiku ($HAIKU): open extraction"
  corpus_blob | run_claude "$SCRIPT_DIR/extract_pass1_haiku.md" "$HAIKU" > "$OUT/pass1.json"
  echo "  -> $OUT/pass1.json"

  say "Pass 2 — Sonnet ($SONNET): schema unification"
  cat "$OUT/pass1.json" | run_claude "$SCRIPT_DIR/unify_schema_sonnet.md" "$SONNET" > "$OUT/schema.json"
  echo "  -> $OUT/schema.json"

  say "Pass 3 — Haiku ($HAIKU): schema-constrained re-extraction"
  { printf 'CANONICAL SCHEMA (schema.json):\n'; cat "$OUT/schema.json";
    printf '\n\nPASSAGES:\n'; corpus_blob; } \
    | run_claude "$SCRIPT_DIR/extract_pass2_haiku.md" "$HAIKU" > "$OUT/frames.json"
  echo "  -> $OUT/frames.json"
else
  say "Skipping extraction; reusing $OUT/frames.json"
  if [ ! -f "$OUT/frames.json" ]; then
    cp "$ROOT/sources/tides/extraction/frames.json" "$OUT/frames.json"
    cp "$ROOT/sources/tides/extraction/schema.json" "$OUT/schema.json" 2>/dev/null || true
    echo "  (copied committed extraction into $OUT)"
  fi
fi

# Reproducibility signal: does the fresh extraction still match the committed,
# machine-checked frames? (Non-fatal — informational.)
COMMITTED="$ROOT/sources/tides/extraction/frames.json"
if [ -f "$COMMITTED" ] && [ "$OUT/frames.json" -ef "$COMMITTED" ]; then
  : # ran --in-place; nothing to diff against
elif [ -f "$COMMITTED" ]; then
  if diff -q <(jq -S .frames "$COMMITTED") <(jq -S .frames "$OUT/frames.json") >/dev/null 2>&1; then
    echo "  reproducibility: fresh frames MATCH the committed machine-checked frames."
  else
    echo "  reproducibility: fresh frames DIFFER from committed (expected under model variance)."
    echo "                   see: diff <(jq -S .frames $COMMITTED) <(jq -S .frames $OUT/frames.json)"
  fi
fi

if [ "$NO_LEAN" -eq 1 ]; then
  say "Done (--no-lean). Frames at $OUT/frames.json"
  exit 0
fi

say "Lean — running the verified STE definitions on $OUT/frames.json"
command -v lake >/dev/null || { echo "lake not found on PATH" >&2; exit 1; }
cd "$ROOT/lean"
# The `tides` exe reads the JSON at runtime and evaluates STE.Consistent /
# STE.disagreementDegree (the definitions proved correct in Ste.FiniteInstance).
lake build tides >/dev/null
lake exe tides "$OUT/frames.json"
