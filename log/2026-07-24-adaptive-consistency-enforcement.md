# 2026-07-24 — Enforcement half of adaptive consistency + width link

Branch: `research/consistency-enforcement`.
New module: `lean/Ste/BucketConsistency.lean` (imported from `lean/Ste.lean`).
CI: workflow "Lean", run **#105** (id 30084431466), commit `267bb16`,
**conclusion = success**, first attempt. No `sorry`, `admit`, `axiom`,
or `native_decide` anywhere in the module (grep-verified; the only
textual hit is the English word "admits" in a docstring).
Lit review: `papers/notes/adaptive-consistency-litreview.tex`, built with
pdflatex ×2 + bibtex against `refs.bib` (8 new entries appended):
8 pages, 0 errors, 0 undefined citations/references.

Rule applied throughout: **distrust results that aren't machine proven.**
Everything below is labelled machine-proved (verbatim statement) or open.

## The target

Open problem (from `Ste.AdaptiveConsistency`, "Honest scope" item (2)):

(a) **Enforcement** — bucket elimination (join-then-project per bucket)
*establishes* directional consistency while *preserving* the solution
set, i.e. adaptive consistency is a complete solver, cost exponential
only in the induced width.

(b) **Width link** — connect `SepWidthLE sep w` of
`Ste.AdaptiveConsistency` to `AchievesWidth` / `inducedTreewidth` of
`Ste.Treedecomp` (and thence `Ste.GraphTreewidth`).

## What closed in Lean (verbatim statements, all CI-verified)

### Part 1 — enforcement at the joint-constraint level

The projective bucket step (`projectBucketHead v B` = bucket of `v`
joined, then `project`ed; message is *definitionally* the projection of
the joined bucket):

```lean
theorem joinConstraint_projectBucketStep (v : V)
    {B : List (Finset V × Set (∀ v, A v))}
    (h : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V)) :
    joinConstraint (projectBucketStep v B)
      = project (joinConstraint B) v
```
— exact solution-set preservation: the residual state's joint
constraint IS the projection of the previous one.

```lean
theorem exists_update_mem_of_mem_projectBucketStep (v : V)
    {B : List (Finset V × Set (∀ v, A v))}
    (h : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V))
    {f : ∀ v, A v} (hf : f ∈ joinConstraint (projectBucketStep v B)) :
    ∃ a : A v, Function.update f v a ∈ joinConstraint B
```
— the step establishes the extension property at the eliminated
variable (enforcement direction, instance form).

```lean
theorem joinConstraint_projectBucketEliminate (vs : List V)
    {B : List (Finset V × Set (∀ v, A v))}
    (h : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V)) :
    joinConstraint (projectBucketEliminate vs B)
      = projectEliminate vs (joinConstraint B)

theorem projectBucketEliminate_nonempty_iff (vs : List V)
    {B : List (Finset V × Set (∀ v, A v))}
    (h : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V)) :
    (joinConstraint (projectBucketEliminate vs B)).Nonempty
      ↔ (joinConstraint B).Nonempty

theorem projectBucketEliminate_decides [Nonempty (∀ v, A v)]
    {vs : List V} {B : List (Finset V × Set (∀ v, A v))}
    (hsupp : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V))
    (hcover : ∀ q ∈ B, (↑q.1 : Set V) ⊆ projected vs) :
    (joinConstraint (projectBucketEliminate vs B) = Set.univ
        ↔ (joinConstraint B).Nonempty)
      ∧ (joinConstraint (projectBucketEliminate vs B) = ∅
        ↔ joinConstraint B = ∅)
```
— projective bucket elimination is a complete solver (unconditional
verdict; contrast the substituted verdict of `bucketEliminate_decides`).

```lean
theorem exists_extension_of_mem_projectBucketEliminate :
    ∀ (vs : List V) {B : List (Finset V × Set (∀ v, A v))},
      (∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V)) →
      ∀ {f : ∀ v, A v}, f ∈ joinConstraint (projectBucketEliminate vs B) →
      ∃ g ∈ joinConstraint B, ∀ u, u ∉ projected vs → g u = f u
```
— backtrack-free extraction: survivors extend to original solutions
changing only eliminated variables.

Also: `projectBucketStep_support`, `projectBucketStep_scope_subset`
(invariants), `joinConstraint_subset_projectBucketStep` (soundness, no
support hypothesis needed).

### Part 2 — relative directional consistency suffices (new theorem)

**Research finding.** `DirectionalConsistent` in
`Ste.AdaptiveConsistency` demands witnesses for *every*
domain-respecting assignment. What bucket elimination establishes (and
what Dechter's directional consistency actually says) is *relative*:
witnesses only for assignments satisfying the earlier buckets — where
the recorded messages live. As previously formalized, the repo's easy
half consumed a hypothesis strictly stronger than what enforcement can
supply; the two halves did not compose. Closed by:

```lean
def BucketRelativeConsistent {n : ℕ} (D : Fin (n + 1) → Set α)
    (R : Fin n → (Fin (n + 1) → α) → Prop) : Prop :=
  ∀ i : Fin n, ∀ g : Fin (n + 1) → α, (∀ u, g u ∈ D u) →
    (∀ j : Fin n, j.val < i.val → R j g) →
    ∃ c ∈ D i.succ, R i (Function.update g i.succ c)

theorem bucketRelativeConsistent_solvable {n : ℕ}
    {D : Fin (n + 1) → Set α} {sep : Fin n → Finset (Fin (n + 1))}
    {R : Fin n → (Fin (n + 1) → α) → Prop}
    (hsep : ∀ i : Fin n, ∀ u ∈ sep i, u.val ≤ i.val)
    (hdep : SepSupported sep R)
    (hRC : BucketRelativeConsistent D R)
    (hne : ∀ u, (D u).Nonempty) :
    ∃ f, AdaptiveSolution D R f
```
(plus the through-a-root-value form
`bucketRelativeConsistent_solvable_from`). Proof method: guard each
bucket by its predecessors (`guardedR`), prove
`adaptiveSolution_guardedR_iff` (same solution set, strong induction),
`guardedR_sepSupported` (prefix separators), and
`guardedR_directionalConsistent` (relative ⇒ unconditional for the
guarded net, because an update at `i.succ` is invisible to earlier
buckets), then reuse the existing greedy engine. No new induction.

### Part 3 — width link

```lean
theorem projectBucketBags_map_fst (order : List ((v : V) × A v)) :
    ∀ {B B' : List (Finset V × Set (∀ v, A v))},
      B.map Prod.fst = B'.map Prod.fst →
      (projectBucketBags (order.map Sigma.fst) B).map Prod.fst
        = (bucketBags order B').map Prod.fst
```
— projective and substitutive runs have identical scope traces, so
`Ste.Treedecomp`'s width accounting transfers verbatim
(`projectBucketBags_card_le`).

```lean
theorem runSep_eq_messageScope {n : ℕ}
    (B : List (Finset (Fin (n + 1)) × Set (Fin (n + 1) → α))) (i : Fin n) :
    runSep B i
      = (projectBucketHead i.succ
          (projectBucketEliminate
            ((decreasingOrder n).take (n - 1 - i.val)) B)).1

theorem runSep_precedes {n : ℕ}
    (B : List (Finset (Fin (n + 1)) × Set (Fin (n + 1) → α))) :
    ∀ i : Fin n, ∀ u ∈ runSep B i, u.val ≤ i.val

theorem runSep_widthLE {n : ℕ}
    {B : List (Finset (Fin (n + 1)) × Set (Fin (n + 1) → α))} {w : ℕ}
    (h : ∀ q ∈ projectBucketBags (decreasingOrder n) B, q.1.card ≤ w) :
    SepWidthLE (runSep B) w

theorem runSep_link {n : ℕ} [Nonempty α] {w : ℕ}
    (B : List (Finset (Fin (n + 1)) × Set (Fin (n + 1) → α)))
    (order : List ((v : Fin (n + 1)) × α))
    (hfst : order.map Sigma.fst = decreasingOrder n)
    (hcov : ∀ q ∈ B, (↑q.1 : Set (Fin (n + 1))) ⊆ eliminated order)
    (hw : ∀ q ∈ bucketBags order B, q.1.card ≤ w + 1) :
    (∀ i : Fin n, ∀ u ∈ runSep B i, u.val ≤ i.val)
      ∧ SepWidthLE (runSep B) (w + 1)
      ∧ inducedTreewidth B ≤ w
```
— the separators the run records ARE `bucketHead`-style message scopes,
are topologically ordered (the `hsep` hypothesis of
`Ste.AdaptiveConsistency`, now established rather than assumed), and
satisfy `SepWidthLE` at the `AchievesWidth`/`inducedTreewidth` budget of
the same order. Via `treewidth_primalGraph_le` this reaches graph
treewidth.

## What did NOT close, and why

1. **Per-node reassembly (the remaining gap in (a)).** Not mechanized:
   packaging the final state of the `Fin (n + 1)` decreasing run as a
   literal bucket network `(D, runSep B, R)` with
   `adaptiveSet D R = joinConstraint B` and
   `BucketRelativeConsistent D R`. This needs constraint-to-bucket
   provenance (each constraint joins the bucket of its maximal
   variable), tracking which recorded message lands in which lower
   bucket, and root-domain extraction (surviving scope-⊆-{0}
   constraints become `D 0`). Attempted scoping put this at several
   hundred lines of index bookkeeping with real risk of not landing;
   Part 1 (joint-constraint completeness + extraction) and Part 2
   (sufficiency of the exact condition enforcement provides) were
   proved instead, and their composition into the per-node statement is
   argued on paper in the lit review, not in Lean.
2. **General elimination orders in the width link.** `runSep_*` is for
   the decreasing order — the order implicit in the
   `Ste.AdaptiveConsistency` numbering. Arbitrary orders classically
   reduce to it by renumbering variables; the permutation transport of
   instances/networks is not mechanized.
3. **Time complexity.** Untouched, as before: only table-space bounds
   exist (`bucketEliminate_total_space`,
   `bucketEliminate_treewidth_bound`). "Exponential only in w" is
   machine-proved for space, literature-cited for time.

## Verdict

**Partially achieved — substantial, honest progress; not fully closed.**
Machine-proved: (i) bucket elimination with the projective (∃) step
preserves the solution set *exactly* at every step, decides feasibility
unconditionally, and admits backtrack-free extraction — the
completeness of adaptive consistency at the joint-constraint level;
(ii) the *relative* directional-consistency condition (the one
enforcement actually provides — a mismatch with the repo's previous
`DirectionalConsistent` that this work surfaced) suffices for
backtrack-free solvability; (iii) the separators recorded by the run
coincide with `bucketHead` message scopes, are topologically ordered,
and link `SepWidthLE` to `AchievesWidth`/`inducedTreewidth` on the
decreasing order. Open: the per-node reassembly of the run's final
state into a `BucketRelativeConsistent` bucket network with
`adaptiveSet = joinConstraint` (the last inch of (a)), general-order
renumbering in (b), and any time-complexity model.

## New conjectures for the queue

- **R-reassembly.** For the decreasing run on `Fin (n + 1)` with
  `A = const α`: define `R i g := g ∈ joinConstraint (bucket at the
  step eliminating i.succ)` and `D 0` from the final residual state;
  conjecture `adaptiveSet D R = joinConstraint B` and
  `BucketRelativeConsistent D R` (with `SepSupported (runSep B) R` via
  `hasSupport_joinConstraint` + the scope invariant). This would close
  gap 1; all needed invariants except provenance are already in the
  module.
- **Permutation transport.** A `reindex : (Fin (n+1) ≃ V) → instance →
  instance` with `joinConstraint`/`bucketBags`/width equivariance,
  reducing arbitrary elimination orders to the decreasing one; would
  upgrade `runSep_link` to quantify over the optimal order and hence
  bound `SepWidthLE` by `inducedTreewidth B + 1` directly.
- **Converse width link.** From `SepWidthLE sep w` + `SepSupported`
  for an *abstract* bucket network, construct an instance `B` whose
  `inducedTreewidth` is ≤ w (the direction opposite to `runSep_link`),
  making the two width measures provably equal, not just mutually
  bounded.
- **Tightness of relativization.** Exhibit (decidably, small `n`) a
  run output that is `BucketRelativeConsistent` but not
  `DirectionalConsistent` — certifying in Lean that the Part-2
  weakening is strict and necessary.
