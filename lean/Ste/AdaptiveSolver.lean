/-
Adaptive consistency as a complete, width-bounded solver.

`Ste.BucketConsistency` proved the three ingredients separately:

* **enforcement / solution-set preservation** — the projective bucket
  fold computes `projectEliminate` of the joint constraint, losing and
  inventing no solution (`joinConstraint_projectBucketEliminate`);
* **decision** — a complete order collapses the final state to `univ`
  (feasible) or `∅` (infeasible) (`projectBucketEliminate_decides`);
* **backtrack-free extraction** — any point of the final state extends
  to a solution of the original instance, touching only eliminated
  variables (`exists_extension_of_mem_projectBucketEliminate`);
* **width** — the recorded message scopes obey the elimination-width
  accounting of `Ste.Treedecomp` (`runSep_link`, `projectBucketBags_card_le`).

What was missing was the *single statement* fusing them: "adaptive
consistency is a complete, width-bounded solver."  This file states and
proves it, in two forms.

* `projectBucketEliminate_complete_solver` — for an arbitrary complete
  elimination order achieving width `w`: the run decides feasibility
  AND, when feasible, returns a concrete global solution, all within
  induced treewidth `w`.  This is the fused theorem at the
  joint-constraint (algorithmic) level.

* `decreasingRun_adaptiveSolver` — adaptive consistency proper: run the
  decreasing order `[n, …, 1]` that keeps the root.  Feasibility is
  decided by the root-domain residue (the final state), a solution is
  extracted backward through any feasible root value, and the separators
  are the algorithm's OWN recorded scopes `runSep B` — topologically
  ordered and width-bounded, with `inducedTreewidth B ≤ w`.  This is the
  form that lines up with the `Fin (n + 1)` bucket-network numbering of
  `Ste.AdaptiveConsistency`.

References: R. Dechter, *Constraint Processing*, Morgan Kaufmann 2003,
ch. 4 (`dechter2003constraint`); R. Dechter, *Bucket elimination*,
Artificial Intelligence 113 (1999) (`dechter1999bucket`); R. Dechter and
J. Pearl, Artificial Intelligence 34 (1987) (`dechterpearl1987network`).
-/
import Ste.BucketConsistency

namespace STE

open Set

variable {V : Type*} {A : V → Type*} [DecidableEq V]

/-! ### The fused solver, at the joint-constraint level -/

/-- **Adaptive consistency is a complete, width-bounded solver.**  Fix a
base point `f₀` and an elimination `order` that is *complete* for `B`
(its variables cover every constraint scope) and materializes only
substitutive bags of at most `w + 1` variables.  Run projective bucket
elimination along it.  Then, all in one statement:

* (decide feasible) the final joint constraint is `Set.univ` iff the
  instance is feasible;
* (decide infeasible) it is `∅` iff the instance is infeasible;
* (solve) when feasible, a concrete global solution `g ∈ joinConstraint B`
  is produced by backtrack-free extraction, agreeing with the base point
  `f₀` off the eliminated variables — no search, no retraction;
* (width) `inducedTreewidth B ≤ w`, so the whole run stays within width
  `w + 1`.

This fuses the enforcement half (solution-set preservation), the
decision, the extraction, and the width accounting of
`Ste.BucketConsistency` into the single theorem that projective bucket
elimination solves bounded-width STE completely. -/
theorem projectBucketEliminate_complete_solver [Nonempty (∀ v, A v)]
    (f₀ : ∀ v, A v)
    {B : List (Finset V × Set (∀ v, A v))}
    (order : List ((v : V) × A v)) {w : ℕ}
    (hsupp : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V))
    (hcover : ∀ q ∈ B, (↑q.1 : Set V) ⊆ eliminated order)
    (hwidth : ∀ q ∈ bucketBags order B, q.1.card ≤ w + 1) :
    (joinConstraint (projectBucketEliminate (order.map Sigma.fst) B) = Set.univ
        ↔ (joinConstraint B).Nonempty)
      ∧ (joinConstraint (projectBucketEliminate (order.map Sigma.fst) B) = ∅
        ↔ joinConstraint B = ∅)
      ∧ ((joinConstraint B).Nonempty →
          ∃ g ∈ joinConstraint B, ∀ u, u ∉ eliminated order → g u = f₀ u)
      ∧ inducedTreewidth B ≤ w := by
  -- `eliminated order` and `projected (order.map Sigma.fst)` are the
  -- same set (both `{u | u ∈ order.map Sigma.fst}`), so the cover
  -- hypothesis feeds the projective decision directly.
  have hcover' : ∀ q ∈ B,
      (↑q.1 : Set V) ⊆ projected (order.map Sigma.fst) :=
    fun q hq => hcover q hq
  have hdec := projectBucketEliminate_decides hsupp hcover'
  refine ⟨hdec.1, hdec.2, ?_, inducedTreewidth_le ⟨order, hcover, hwidth⟩⟩
  intro hne
  have huniv :
      joinConstraint (projectBucketEliminate (order.map Sigma.fst) B) = Set.univ :=
    hdec.1.mpr hne
  have hf0 :
      f₀ ∈ joinConstraint (projectBucketEliminate (order.map Sigma.fst) B) := by
    rw [huniv]; exact Set.mem_univ _
  obtain ⟨g, hg, hgf⟩ :=
    exists_extension_of_mem_projectBucketEliminate (order.map Sigma.fst) hsupp hf0
  exact ⟨g, hg, fun u hu => hgf u hu⟩

end STE

namespace STE

open Set

variable {α : Type*}

/-! ### Adaptive consistency proper: the decreasing run and its own
separators -/

/-- **Adaptive consistency solves the bucket network within its own
recorded width.**  Run the decreasing order `[n, …, 1]` — the one that
keeps the root, matching the `Fin (n + 1)` numbering of
`Ste.AdaptiveConsistency` — on a scoped instance `B`, along a
substitutive `order` witnessing width `w`.  Then:

* (decide) the instance is feasible iff the final (root-domain) state is
  nonempty — feasibility read off a single residual constraint on the
  root;
* (extract) every point `f` of the final state extends to a global
  solution `g ∈ joinConstraint B`, modifying only eliminated
  (non-root) variables — backtrack-free;
* (separators, ordered) the algorithm's own recorded message scopes
  `runSep B i` precede their node — the topological hypothesis of the
  solvability theorems, discharged by the run;
* (separators, width) `SepWidthLE (runSep B) (w + 1)`;
* (width) `inducedTreewidth B ≤ w`.

The separators here are *produced by the algorithm*, not postulated:
`runSep B` is the trace of message scopes the projective decreasing run
materializes (`Ste.BucketConsistency`). -/
theorem decreasingRun_adaptiveSolver {n : ℕ} [Nonempty α]
    {B : List (Finset (Fin (n + 1)) × Set (Fin (n + 1) → α))}
    (order : List ((v : Fin (n + 1)) × α)) {w : ℕ}
    (hfst : order.map Sigma.fst = decreasingOrder n)
    (hsupp : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set (Fin (n + 1))))
    (hcov : ∀ q ∈ B, (↑q.1 : Set (Fin (n + 1))) ⊆ eliminated order)
    (hw : ∀ q ∈ bucketBags order B, q.1.card ≤ w + 1) :
    ((joinConstraint (projectBucketEliminate (decreasingOrder n) B)).Nonempty
        ↔ (joinConstraint B).Nonempty)
      ∧ (∀ f ∈ joinConstraint (projectBucketEliminate (decreasingOrder n) B),
          ∃ g ∈ joinConstraint B,
            ∀ u, u ∉ projected (decreasingOrder n) → g u = f u)
      ∧ (∀ i : Fin n, ∀ u ∈ runSep B i, u.val ≤ i.val)
      ∧ SepWidthLE (runSep B) (w + 1)
      ∧ inducedTreewidth B ≤ w := by
  have hlink := runSep_link B order hfst hcov hw
  refine ⟨projectBucketEliminate_nonempty_iff (decreasingOrder n) hsupp,
    fun f hf =>
      exists_extension_of_mem_projectBucketEliminate (decreasingOrder n) hsupp hf,
    hlink.1, hlink.2.1, hlink.2.2⟩

end STE
