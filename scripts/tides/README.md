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

The extraction runs on **Claude Haiku 4.5** (passes 1 & 3) and **Claude Sonnet** (pass 2), invoked
through the Claude Code agent harness (`Agent` tool with `model: haiku` / `model: sonnet`). The
prompts above are the committed, reusable templates; re-running them on the same corpus reproduces
the frames. Downstream, `lean/Ste/TidesCorpus.lean` encodes the final frames and proves the STE
invariants (feasibility, minimal conflicting core, consensus after dropping the outlier).
