# 2026-07-24 — Empirical STE run: the multi-voice "cause of the tides" corpus

First end-to-end empirical instance of set-theoretic estimation: acquire a
corpus of authors on one topic, extract structured frames with Claude Haiku,
verify the disagreement's invariants in Lean.

## Pipeline (schema NOT fixed up front)
- Stage 0 corpus: 7 public-domain passages in `sources/tides/` (Pliny, Bede,
  Kepler, Galileo, Descartes, Newton, Laplace).
- Pass 1 (Haiku 4.5, open): per-author (variable,value,quote) + ~25 candidate
  variables → `sources/tides/extraction/pass1.json`.
- Pass 2 (Sonnet, unify): canonical 7-variable schema with closed domains +
  synonym map → `schema.json`.
- Pass 3 (Haiku 4.5, constrained): re-extract every author against the schema
  → `frames.json`.
- Prompts committed + reusable in `scripts/tides/`. Extraction ran through the
  agent harness (Agent tool, model: haiku / sonnet), since no raw API key is
  reachable from a shell in this environment.

## Lean verification — `Ste.TidesCorpus` (CI-green, run #124)
Each author = an STE property set; feasibility = `feasibilitySet` (Ste.Basic).
- `feasible_eq_empty`: corpus globally inconsistent.
- `kepler_galileo_core`, `kepler_descartes_core`, `galileo_descartes_core`:
  the three-way moonRole split (attraction/pressure/rejected) → three 2-author
  minimal cores.
- `pliny_kepler_mechanism_core`: even the attraction camp splits on mechanism
  → disagreement is pervasive, not one outlier.
- `attraction_camp_moon_consistent` + `descartes_dissents` + `galileo_dissents`:
  on moonRole, the 5-author attraction camp shares a reading; exactly two
  dissent.
- `no_fair_reading`: Combettes inconsistency corollary.

## What the machine corrected
The plan predicted ONE outlier (Galileo) with a consensus after dropping him.
The run refuted both: TWO dissenters on moonRole (Galileo rejected, Descartes
pressure), and the attraction camp is itself split on mechanism (direct /
gravitational / dynamical). The coupling is layered and pervasive. Exactly the
value of a machine-checked empirical instance: the verdict overturned the story.

## Boundary of trust
Lean certifies the aggregation, not the reading. Every frame value in
`frames.json` carries its licensing quote (auditable); invariants are
conditional on the frames. Passages are curated public-domain representative
statements (provenance in refs.bib).

## Next (plan phase P2)
The quantitative invariants (concept lattice, rho / Cech obstruction,
treewidth) need the computable Finset refinement run on this instance; the
qualitative feasibility verdict is complete.
