# 2026-07-24 — A computable STE layer, and the tides invariants computed by the kernel

## What and why

The tides corpus (`Ste.TidesCorpus`) proved its qualitative verdict —
empty feasibility set, minimal conflicting cores, dissent structure — with
hand-written `Set` arguments. That is trustworthy but not *executable*: the
numbers (how many ways `moonRole` splits, how many variables actually
carry the disagreement) were computed off-machine and asserted in prose.

This step closes the gap requested as plan phase **P2**: make the STE
aggregation *computable* in Lean and prove the computable layer agrees with
the verified `Set`-based spec of `Ste.Basic`.

## The key structural fact

For a **finite frame corpus** — each author `a` fixing a partial
assignment `frame a : V → Option W` (silence = `none`) — joint
satisfiability is *not* a genuinely `Set`-level question. It collapses to a
**decidable, pairwise** one:

> the corpus is jointly satisfiable **iff** no two authors ever assign the
> same variable two different values.

`Ste.FiniteInstance` proves that collapse in general:

- `frameConstraint frame a` — the property set of author `a` (the general
  form of `TidesCorpus.constraint`).
- `compatibleOn frame v a b` — decidable pairwise compatibility on a
  variable, written as a disjunction so the kernel can decide it.
- `Consistent frame := ∀ v a b, compatibleOn frame v a b` — a `Decidable`
  predicate (via `Fintype V`, `Fintype A`, `DecidableEq W`).
- `frameWitness` — the canonical reading assembled from a consistent
  corpus; `frameWitness_mem` proves it satisfies every author.
- **The bridge**: `nonempty_iff_consistent` and its corollary
  `feasibilitySet_eq_empty_iff : feasibilitySet (frameConstraint frame) = ∅
  ↔ ¬ Consistent frame`. The left side is the verified `Ste.Basic` spec;
  the right side is decided by the kernel. Nothing is trusted that the
  kernel has not checked.

The quantitative refinement:

- `assertedValues frame v` — the `Finset` of distinct values variable `v`
  receives across the corpus (`mem_assertedValues` characterizes it).
- `disagreementDegree frame v := (assertedValues frame v).card`.
- `agree_iff_degree_le_one` — a variable is unanimous-where-spoken iff its
  degree is `≤ 1`.

## The tides corpus, computed

`Ste.TidesComputable` instantiates the bridge on the actual frames.
`constraint = frameConstraint frame` holds **by `rfl`**, so every general
theorem specializes with no glue. Then the kernel computes:

- `tides_inconsistent : ¬ Consistent frame` — **by `decide`**.
- `feasible_eq_empty_computed : feasibilitySet constraint = ∅` — the *same
  statement* as `TidesCorpus.feasible_eq_empty`, now obtained by feeding the
  decided inconsistency through the bridge. The computable route reproduces
  the hand proof.
- The **disagreement degrees**, each by `decide`:
  `primaryCause = 3`, `moonRole = 3`, `mechanism = 5`, `sunRole = 2`,
  `springNeap = 1`, `earthMotion = 1`, `quantitative = 1`.
- `conflictVars_card : conflictVars.card = 4` and
  `conflictVars_eq : conflictVars = {primaryCause, moonRole, mechanism,
  sunRole}` — **exactly four variables carry the disagreement**, computed.
- `springNeap_unanimous` — a positive fact obtained *through* the
  degree characterization (`agree_iff_degree_le_one.mp (by decide)`):
  every author who mentions spring/neap dependence agrees.
- `#eval degreeReport` / `#eval decide (Consistent frame)` — the same
  invariants dumped executably (outside the trusted proof).

## Trust boundary

`decide` uses the Lean **kernel** — no `native_decide`, so the compiler
stays out of the TCB, consistent with the project's standing rule to
distrust anything not machine-proven. The invariants are conditional on the
extracted frames (each licensed by a source quote in `frames.json`); the
Lean layer certifies the aggregation, not the reading of the text.

## Files

- `lean/Ste/FiniteInstance.lean` — the general computable layer (new).
- `lean/Ste/TidesComputable.lean` — the tides instantiation (new).
- `lean/Ste/TidesCorpus.lean` — `Var`/`Author` now `deriving Fintype`,
  `Val` `deriving Inhabited`, `Var` `deriving Repr` (for `#eval`).
- `lean/Ste.lean` — imports both new modules.

Branch `research/computable-ste` → CI green → merged to main.
