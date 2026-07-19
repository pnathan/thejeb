# 2026-07-19 — Project bootstrap

## Goal
Stand up the STE mechanization project: pull the two seed papers, set up
Lean + CI, mechanize the STE core, and scaffold the writing.

## Actions
- Downloaded seed papers to `sources/`:
  - Combettes 1993 from the author's page (`pcombet.math.ncsu.edu/proc.pdf`).
  - Carlson 2012 dissertation. ResearchGate (the only host) is behind
    Cloudflare and returns HTTP 403/1020 to curl and to a headless
    Chromium `page.request`. Recovered a clean `application/pdf` copy from
    the Internet Archive snapshot `20240713055533id_/…` of the RG
    full-text. Verified: 166-page PDF, front matter confirms
    "University of Idaho, May 2012, advisors Hiromoto & Wells".
- Established repo layout per project rules: `sources/`, `lean/`, `log/`,
  `papers/notes/`, `papers/papers/`, `annotated-bibliography.tex`,
  `refs.bib`.

## Notes / constraints discovered
- **Egress policy blocks GitHub release assets.** `elan` cannot download a
  Lean toolchain (`releases.lean-lang.org` 302 → `github.com/.../releases`
  → 403), and the GitHub API is gated ("use add_repo"). Consequence: we
  **cannot build Lean locally in this environment**. Mitigation: the
  GitHub Action *is* the verifier — every push to `main` builds the `Ste`
  library via `leanprover/lean-action`. Per the project rule "distrust
  results that aren't machine proven," Lean results are treated as
  unverified until the corresponding CI run is green.
- Mathlib pinned to `v4.32.0`. `lake-manifest.json` was hand-assembled
  from mathlib4's own `v4.32.0` manifest (deps marked `inherited`) so the
  build is reproducible without a local `lake update`.

## Result
Sources + Lean skeleton + CI pushed to `main`. First CI run
(`29689677312`) built all four `Ste` modules successfully against the
Mathlib cache in ~2m18s → the STE core is machine-verified.
