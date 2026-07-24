# 2026-07-24 — A large (86-document) corpus through the STE pipeline: The Federalist Papers

## What and why

The tides corpus was seven short passages. The next question was whether the
same STE pipeline scales to a *large* corpus of *long* documents, with a
chunking system so each document is extracted in focused pieces. Requirement:
not fewer than 50 documents.

Corpus: **The Federalist Papers** — 86 essays (85 numbers; No. 70 appears
twice in this edition), split from Project Gutenberg eBook #18 (public domain)
into `sources/federalist/fed_NNN.txt`, one file per essay with a provenance
header (`scripts/federalist/split_corpus.py`). Median essay ≈ 13k characters,
max ≈ 34k — genuinely long enough to need chunking. Topic: the design and
defense of the proposed U.S. Constitution.

## The pipeline (general, chunking, parallel)

`scripts/corpus/` is a topic-parameterized generalization of the tides
pipeline:

1. **Pass 1 — Haiku, open extraction, per chunk.** Each document is split into
   ~9k-char chunks (`chunk_text`, on paragraph boundaries); every chunk is
   extracted independently into `(variable, value, quote)` claims; the
   chunk-level claims are unioned per document. 86 docs → **189 chunks**.
2. **Pass 2 — Sonnet, schema unification, once.** The 189 chunks proposed
   **2,510 distinct (variable, value) pairs**; Sonnet merged them into a
   canonical **10-variable** schema with closed domains and a synonym map.
3. **Pass 3 — Haiku, schema-constrained, per document.** Each of the 86 docs is
   re-extracted against the canonical schema into one frame (value or
   `silent` per variable, with a licensing quote).

Model calls run in parallel (`--jobs 8`); the run made ≈ 276 calls
(189 + 1 + 86) in roughly half an hour. Output shape is exactly what the
verified Lean `tides` exe reads.

## The verdict — computed by the proved algorithm

`lake exe tides build/federalist/frames.json` ran the **verified**
`STE.Consistent` / `STE.disagreementDegree` (`Ste.FiniteInstance`) over the 86
document-voices and 10 variables:

- **`STE.Consistent` = false** — the corpus is inconsistent; feasibility set
  empty. Even 86 essays by one pseudonymous author (Publius) do not admit a
  single joint reading.
- But the inconsistency is **narrow**, unlike the tides. **7 of 10 variables
  are unanimous where spoken** (disagreement degree ≤ 1): ratification stance,
  union vs. disunion, the standing-army restriction, executive structure,
  judicial power, bill-of-rights necessity, and extended-republic theory.
  That is a large **consistent core**.
- **3 conflict sites** carry the whole obstruction:
  - `government_character` — **degree 3**, a genuine three-way split:
    `mixed_composite` (25 essays, incl. Fed 39's *"neither a national nor a
    federal Constitution, but a composition of both"*), `federal_confederacy`
    (11 essays, e.g. Fed 45 *"powers delegated…few and defined"*),
    `national_consolidated` (2 essays, e.g. Hamilton's Fed 12/15).
  - `federal_power_scope` — degree 2 (32 extensive vs. 13 strictly-limited).
  - `senate_equal_suffrage` — degree 2 (5 justified-compromise vs. 1 unjust).

The machine recovered the real, well-documented internal tension of The
Federalist: Publius characterizes the proposed government three different ways
depending on rhetorical need, and the essays differ on the reach of federal
power. Seven other axes are unanimous — the shared Federalist program.

## Contrast with the tides

| | Tides (7 voices) | Federalist (86 voices) |
|---|---|---|
| Consistent? | No | No |
| Structure | pervasive, multi-camp | large consistent core + 3 conflict sites |
| Worst variable | mechanism (deg 5) | government_character (deg 3) |
| Reading | many rival theories | one program, a few internal tensions |

Same verified algorithm, two qualitatively different disagreement shapes —
which is the point of computing the verdict rather than asserting it.

## Trust boundary

The verdict is the verified `STE.Consistent`/`disagreementDegree` evaluated on
runtime data (no `native_decide`; the definitions are the ones proved correct
in `Ste.FiniteInstance`). It is conditional on the extraction: each asserted
value carries the licensing quote in `frames.json`, so every cell is auditable
against the essay, but a mis-extraction would move a count. The three conflict
sites were spot-checked against quotes and are faithful.

## Files

- `sources/federalist/fed_*.txt` — the 86-essay corpus (public domain).
- `scripts/federalist/split_corpus.py` — the splitter.
- `scripts/corpus/` — the general chunking pipeline (`extract_corpus.py`,
  `run.sh`, `prompts/`).
- `sources/federalist/extraction/{schema.json, frames.json}` — the canonical
  schema and the 86 auditable document frames.
