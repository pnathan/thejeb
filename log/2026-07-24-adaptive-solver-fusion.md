# 2026-07-24 — Adaptive consistency: the complete, width-bounded solver, fused

## Goal

Close the gap flagged in the notes' outlook: "adaptive-consistency
enforcement is proven sufficient once established, but enforcement +
extraction aren't yet fused into one 'adaptive consistency is a
complete, width-bounded solver' theorem." Also the deeper honest-scope
item (1) of `Ste.BucketConsistency`: the joint-constraint-level solver
and the abstract bucket-network formalism were "joined on paper, not in
Lean."

## What was already proven (separately) in `Ste.BucketConsistency`

- Solution-set preservation: `joinConstraint_projectBucketEliminate`.
- Decision: `projectBucketEliminate_decides` (complete order → univ/∅).
- Backtrack-free extraction: `exists_extension_of_mem_projectBucketEliminate`.
- Width: `runSep_link`, `projectBucketBags_card_le`.

And in `Ste.AdaptiveConsistency` (abstract formalism):
- `adaptiveSet D R`, `AdaptiveSolution D R f`.
- `adaptiveSet_eq_feasibilitySet`.

These were never assembled into one statement, and the two type-worlds
(concrete `List (Finset × Set)` vs abstract `Fin (n+1) → Set α` /
`Fin n → (… → Prop)`) were never connected.

## What this session added — `Ste.AdaptiveSolver` (CI-green, run #116)

### Layer 1 — the fused solver (assembly)

- `projectBucketEliminate_complete_solver`: for any complete order
  achieving width `w`, ONE statement giving (decide feasible ↔ final =
  univ), (decide infeasible ↔ final = ∅), (feasible → concrete solution
  by backtrack-free extraction), and `inducedTreewidth B ≤ w`.
- `decreasingRun_adaptiveSolver`: adaptive consistency proper on the
  root-keeping order `[n,…,1]` — feasibility decided by the root-domain
  residue, solution extracted backward, with the algorithm's OWN
  recorded separators `runSep B` shown ordered, `SepWidthLE (w+1)`, and
  `inducedTreewidth ≤ w`.

### Layer 2 — the bridge (the genuinely open piece)

- `bucketNetworkList D sep R`: the abstract network realized as a scoped
  constraint list — one unary domain constraint per node, one bucket
  constraint `(insert i.succ (sep i), {x | R i x})` per non-root node.
- `joinConstraint_bucketNetworkList`: its joint constraint is
  **literally** `adaptiveSet D R`. This is the identity the note named
  as missing (`adaptiveSet = joinConstraint B`), now mechanized.
- `bucketNetworkList_support`: the list respects its scopes, from
  `SepSupported sep R`.
- `adaptiveNetwork_solved_by_elimination`: projective bucket elimination
  on the network's own constraints decides its solvability AND extracts
  a genuine `AdaptiveSolution D R g` — Part 1 and Part 2 joined in Lean,
  assuming only `SepSupported`.
- `adaptiveNetwork_complete_solver`: with a width-`w` covering order, the
  run collapses to `univ` iff the network is solvable, extracts an
  `AdaptiveSolution`, and stays within
  `inducedTreewidth (bucketNetworkList D sep R) ≤ w`.

## Method / verification

- CI is the only verifier (no local Lean). Layer 1 pushed first
  (run #115 success), then Layer 2 on top (run #116 success), then
  merged to `main` (`e16897d`). Two flagged risk points — the exact form
  of `List.mem_finRange` and the `Nonempty (Fin (n+1) → α)` instance —
  both resolved without a fix.

## Residual (documented, still open)

1. Constructing an explicit width-`w` elimination `order` from a
   separator width bound `SepWidthLE sep w` (the reverse of
   `runSep_link`). The solver theorems take the order as a hypothesis;
   producing it from the bucket-network width is the remaining step.
2. Arbitrary elimination orders (the width link is on the decreasing
   order; a general order needs a permutation argument).
3. Time complexity (only table-space bounds exist).

## References

Dechter, *Bucket elimination*, AIJ 113 (1999); Dechter, *Constraint
Processing*, MK 2003, ch. 4; Dechter & Pearl, AIJ 34 (1987); Freuder,
JACM 1982 / 1985; Bodlaender, TCS 209 (1998).
