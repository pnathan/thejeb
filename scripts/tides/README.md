# Tides corpus extraction — three-pass pipeline

The topic is **the cause of the ocean tides**; the corpus is seven public-domain natural
philosophers in `sources/tides/` (Pliny, Bede, Kepler, Galileo, Descartes, Newton, Laplace).

We do NOT fix the schema up front. Instead:

1. **Pass 1 — Haiku, open extraction** (`extract_pass1_haiku.md`). Haiku reads every passage and
   proposes its own (variable, value, quote) claims plus a candidate variable list.
   Output: `sources/tides/extraction/pass1.json`.
2. **Pass 2 — Sonnet, schema unification** (`unify_schema_sonnet.md`). Sonnet merges the
   synonymous variables/values from pass 1 into one canonical schema with closed domains and a
   synonym map. Output: `sources/tides/extraction/schema.json`.
3. **Pass 3 — Haiku, schema-constrained re-extraction** (`extract_pass2_haiku.md`). Haiku
   re-extracts every author against the canonical schema, emitting one assignment per author
   (value or `silent`) with quotes. Output: `sources/tides/extraction/frames.json`.

The extraction runs on **Claude Haiku 4.5** (passes 1 & 3) and **Claude Sonnet** (pass 2). The
prompts above are the committed, reusable templates; re-running them on the same corpus reproduces
the frames.

## Running it locally: `run_pipeline.sh`

```
scripts/tides/run_pipeline.sh              # extract with the `claude` CLI, then run the Lean exe
scripts/tides/run_pipeline.sh --skip-extract   # reuse committed frames.json, just run Lean
scripts/tides/run_pipeline.sh --no-lean        # stop after producing frames.json
scripts/tides/run_pipeline.sh --in-place       # write extraction back into sources/tides/extraction
```

The script drives the whole chain end to end:

```
sources/tides/*.txt
  --(claude -p, haiku)-->  pass1.json      open extraction
  --(claude -p, sonnet)--> schema.json     schema unification
  --(claude -p, haiku)-->  frames.json     schema-constrained re-extraction
  --(lake exe tides)-->    STE verdict + per-variable disagreement report
```

Extraction outputs land in `build/tides/` by default (git-ignored). The script also diffs the
fresh `frames.json` against the committed one as a reproducibility signal.

## The Lean step reads the frames — it does not encode them

`lean/TidesExe.lean` (the `tides` executable) reads `frames.json` **at runtime**, parses it, and
evaluates the *verified* computable STE layer on the loaded data:

- `STE.Consistent` — is the corpus jointly satisfiable? (feasibility set empty iff not, by
  `Ste.FiniteInstance.feasibilitySet_eq_empty_iff`)
- `STE.disagreementDegree` — distinct values asserted per variable
- the conflict sites and the feasibility verdict

Nothing about this corpus is hard-coded in Lean: swap in a different `frames.json` and the same
verified definitions run on it. The trust boundary is the JSON parser plus Lean's evaluator; the
aggregation logic is the one proved correct in `Ste.FiniteInstance`.

`lean/Ste/TidesCorpus.lean` and `lean/Ste/TidesComputable.lean` remain the *statically*
machine-checked companion: they encode the committed frames and prove the same invariants with
`by decide` (kernel), so the committed result is a theorem, while the executable lets any freshly
extracted corpus be scored by the same verified logic.
