# 2026-07-28 — Two camps break the consistent core: Federalist + Anti-Federalist

## The experiment

The single-camp Federalist run (86 essays) found a large *consistent core*: 7
of 10 variables unanimous where spoken, only 3 conflict sites. The obvious
test of whether STE disagreement structure tracks corpus composition: add the
**opposing camp** and re-run.

Corpus: the 86 Federalist essays **plus 73 Anti-Federalist essays** (Brutus,
Cato, Centinel, Federal Farmer, An Old Whig, Philadelphiensis; scraped from
teachingamericanhistory.org, public domain, `scripts/antifederalist/`), for a
**159-document two-camp corpus**. Same general chunking pipeline
(`scripts/corpus/`, now taking multiple corpus dirs), same topic. Pass 1: 262
chunks → 3,253 open (variable,value) pairs; pass 2 (Sonnet) → a canonical
10-variable schema whose domains now carry **both poles** of each question;
pass 3: 159 per-document frames. Scored by the verified `tides` exe
(`STE.Consistent` / `disagreementDegree`, `Ste.FiniteInstance`).

Operational note: the run spanned a multi-day container suspend/resume; the
first pass-3 attempt wedged on stale worker connections. Killing it and
resuming with `--resume` (reusing the cached `pass1.json` / `schema.json`)
recovered cleanly.

## The verdict — the consistent core shatters

**`STE.Consistent` = false**, feasibility set empty. But where the
Federalist-only corpus had 3 conflict sites, the two-camp corpus has **all
10** (every variable has disagreement degree ≥ 2):

| variable | Fed-only degree | two-camp degree |
|---|---|---|
| ratification_stance | 1 | **3** |
| governance_structure | 3 | 3 |
| standing_army_peacetime | 1 | **2** |
| bill_of_rights_necessity | 1 | **2** |
| federal_taxation_scope | (n/a) | **2** |
| executive_power_character | 1 | **2** |
| judiciary_power_scope | 1 | **2** |
| house_representation_adequacy | (n/a) | **2** |
| confederation_adequacy | 1 | **2** |
| senate_character | 2 | **2** |

(Variable names differ slightly between the two schema runs; the point is the
*count* of conflict sites: **3 → 10**.)

## The split is clean and camp-driven

Spot-checks against the extracted frames confirm the disagreement is the
Federalist/Anti-Federalist divide, not extraction noise:

- **ratification_stance**: Federalist essays all `favor_ratification` (78);
  Anti-Federalist essays `oppose_ratification` (55) or
  `favor_with_amendments` (12) — the degree-3 split *is* the two camps plus
  the conditional-ratification wing.
- **bill_of_rights_necessity**: Federalist `unnecessary_or_dangerous` (2, e.g.
  Fed 84); Anti-Federalist `necessary` (25) — cleanly opposite.
- **standing_army_peacetime**: Federalist `necessary_and_safe` 10 vs 2;
  Anti-Federalist `dangerous_to_liberty` 27 vs 1 — a near-perfect camp split,
  with the handful of crossovers reflecting genuine nuance.

## What it demonstrates

The STE disagreement profile is a **function of the corpus, computed by the
proved algorithm** — not a fixed property of the topic. Same verified
`Consistent`/`disagreementDegree`, three qualitatively different shapes now on
record:

- **Tides** (7 voices): pervasively inconsistent, multi-camp, worst variable
  degree 5.
- **Federalist** (86 voices): large consistent core, 3 conflict sites.
- **Ratification, two-camp** (159 voices): total shatter, all 10 variables
  contested, each along the camp line.

Adding the opposing 73 essays flipped 7 unanimous variables into conflicts —
exactly the behavior the must/may/cannot theory predicts (adding information
shrinks the feasible family; here it empties the agreement on every axis).

## Files

- `sources/antifederalist/*.txt` — 73 Anti-Federalist essays (public domain).
- `scripts/antifederalist/fetch_corpus.py` — the scraper/cleaner.
- `sources/ratification/extraction/{schema.json, frames.json}` — the canonical
  10-variable two-camp schema and the 159 auditable document frames.
- `scripts/corpus/extract_corpus.py` — now accepts multiple `--corpus` dirs.
