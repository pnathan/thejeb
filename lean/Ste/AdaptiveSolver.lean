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

/-! ### The bridge: the abstract bucket network IS a scoped instance

`Ste.AdaptiveConsistency` states its formalism abstractly — domains
`D : Fin (n + 1) → Set α`, per-node bucket predicates
`R : Fin n → (Fin (n + 1) → α) → Prop`, solution set `adaptiveSet D R`.
`Ste.BucketConsistency` runs projective elimination on concrete scoped
constraint lists `List (Finset _ × Set _)`.  The honest gap (`Part 1`,
item 1 of its docstring) was that these two are joined only on paper.
Here we join them in Lean: the bucket network is realized as the
concrete list `bucketNetworkList`, whose joint constraint is *literally*
`adaptiveSet D R`, so the projective solver decides and solves the
abstract network. -/

/-- **The bucket network as a scoped constraint list.**  One unary
domain constraint `({v}, {x | x v ∈ D v})` per node, one bucket
constraint `(insert i.succ (sep i), {x | R i x})` per non-root node —
the constraint on the separator `sep i` together with the node
`i.succ`.  Its joint constraint is the network's solution set
(`joinConstraint_bucketNetworkList`). -/
def bucketNetworkList {n : ℕ} (D : Fin (n + 1) → Set α)
    (sep : Fin n → Finset (Fin (n + 1)))
    (R : Fin n → (Fin (n + 1) → α) → Prop) :
    List (Finset (Fin (n + 1)) × Set (Fin (n + 1) → α)) :=
  (List.finRange (n + 1)).map (fun v => ({v}, {x | x v ∈ D v}))
    ++ (List.finRange n).map (fun i => (insert i.succ (sep i), {x | R i x}))

/-- **Solution-set unification**: the joint constraint of the scoped
network list is exactly the abstract solution set `adaptiveSet D R`.
This is the identity the honest-scope note named as missing —
`adaptiveSet D R = joinConstraint B` — now mechanized. -/
theorem joinConstraint_bucketNetworkList {n : ℕ} (D : Fin (n + 1) → Set α)
    (sep : Fin n → Finset (Fin (n + 1)))
    (R : Fin n → (Fin (n + 1) → α) → Prop) :
    joinConstraint (bucketNetworkList D sep R) = adaptiveSet D R := by
  ext f
  rw [mem_joinConstraint, mem_adaptiveSet]
  unfold bucketNetworkList
  constructor
  · intro h
    refine ⟨fun v => ?_, fun i => ?_⟩
    · exact h _ (List.mem_append.mpr (Or.inl
        (List.mem_map.mpr ⟨v, List.mem_finRange v, rfl⟩)))
    · exact h _ (List.mem_append.mpr (Or.inr
        (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)))
  · rintro ⟨hD, hR⟩ q hq
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨v, -, rfl⟩ := List.mem_map.mp hq
      exact hD v
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hq
      exact hR i

/-- **The network list respects its scopes.**  Each unary constraint is
supported on its node; each bucket constraint is supported on
`sep i ∪ {i.succ}` — exactly the separator-dependence `SepSupported`
provides.  This is the hypothesis the projective solver needs. -/
theorem bucketNetworkList_support {n : ℕ} (D : Fin (n + 1) → Set α)
    {sep : Fin n → Finset (Fin (n + 1))}
    {R : Fin n → (Fin (n + 1) → α) → Prop} (hdep : SepSupported sep R) :
    ∀ q ∈ bucketNetworkList D sep R,
      HasSupport q.2 (↑q.1 : Set (Fin (n + 1))) := by
  intro q hq
  unfold bucketNetworkList at hq
  rcases List.mem_append.mp hq with hq | hq
  · obtain ⟨v, -, rfl⟩ := List.mem_map.mp hq
    intro f g hfg
    have hv : f v = g v :=
      hfg v (Finset.mem_coe.mpr (Finset.mem_singleton_self v))
    simp only [Set.mem_setOf_eq, hv]
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hq
    intro f g hfg
    exact hdep i f g
      (fun u hu => hfg u (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hu)))
      (hfg i.succ (Finset.mem_coe.mpr (Finset.mem_insert_self i.succ (sep i))))

/-- **Adaptive consistency, joined in Lean.**  Projective bucket
elimination, run on the network's OWN scoped constraint list along any
order `vs`, solves the abstract bucket network of
`Ste.AdaptiveConsistency`:

* (decide) the network is solvable iff the projective final state is
  nonempty;
* (extract) any point `f` of the final state yields a genuine
  `AdaptiveSolution D R g`, agreeing with `f` off the eliminated
  variables — a backtrack-free witness in the abstract formalism.

Only `SepSupported sep R` is assumed (the network's constraints are
constraints on their scopes).  This closes the paper-only join between
the projective solver (Part 1) and the bucket-network formalism
(Part 2): the two solution sets are literally equal
(`joinConstraint_bucketNetworkList`), so the algorithm operates on the
abstract network directly. -/
theorem adaptiveNetwork_solved_by_elimination {n : ℕ}
    (D : Fin (n + 1) → Set α) (sep : Fin n → Finset (Fin (n + 1)))
    (R : Fin n → (Fin (n + 1) → α) → Prop) (hdep : SepSupported sep R)
    (vs : List (Fin (n + 1))) :
    ((adaptiveSet D R).Nonempty
        ↔ (joinConstraint
            (projectBucketEliminate vs (bucketNetworkList D sep R))).Nonempty)
      ∧ (∀ f ∈ joinConstraint (projectBucketEliminate vs (bucketNetworkList D sep R)),
          ∃ g, AdaptiveSolution D R g ∧ ∀ u, u ∉ projected vs → g u = f u) := by
  have hsupp := bucketNetworkList_support D hdep
  refine ⟨?_, ?_⟩
  · rw [← joinConstraint_bucketNetworkList D sep R]
    exact (projectBucketEliminate_nonempty_iff vs hsupp).symm
  · intro f hf
    obtain ⟨g, hg, hgf⟩ :=
      exists_extension_of_mem_projectBucketEliminate vs hsupp hf
    rw [joinConstraint_bucketNetworkList D sep R, mem_adaptiveSet] at hg
    exact ⟨g, hg, hgf⟩

/-- **The complete, width-bounded solver for the abstract network.**
Given an elimination `order` that covers every scope of the network list
and achieves width `w`, projective bucket elimination on the network's
own constraints:

* (decide) collapses the final joint constraint to `Set.univ` iff the
  network `adaptiveSet D R` is solvable;
* (solve) when solvable, returns a genuine `AdaptiveSolution D R g`,
  agreeing with the base point `f₀` off the eliminated variables;
* (width) within `inducedTreewidth (bucketNetworkList D sep R) ≤ w`.

This is the fully fused statement — enforcement, extraction, decision,
and width — for the abstract bucket-network formalism, not just the
concrete list level.  (Constructing such an `order` from a separator
width bound `SepWidthLE sep w` remains the residual noted in
`Ste.BucketConsistency`, item 2.) -/
theorem adaptiveNetwork_complete_solver {n : ℕ} [Nonempty α]
    (f₀ : Fin (n + 1) → α)
    (D : Fin (n + 1) → Set α) (sep : Fin n → Finset (Fin (n + 1)))
    (R : Fin n → (Fin (n + 1) → α) → Prop) (hdep : SepSupported sep R)
    (order : List ((v : Fin (n + 1)) × α)) {w : ℕ}
    (hcover : ∀ q ∈ bucketNetworkList D sep R,
      (↑q.1 : Set (Fin (n + 1))) ⊆ eliminated order)
    (hwidth : ∀ q ∈ bucketBags order (bucketNetworkList D sep R),
      q.1.card ≤ w + 1) :
    (joinConstraint (projectBucketEliminate (order.map Sigma.fst)
        (bucketNetworkList D sep R)) = Set.univ ↔ (adaptiveSet D R).Nonempty)
      ∧ ((adaptiveSet D R).Nonempty →
          ∃ g, AdaptiveSolution D R g ∧ ∀ u, u ∉ eliminated order → g u = f₀ u)
      ∧ inducedTreewidth (bucketNetworkList D sep R) ≤ w := by
  have hsupp := bucketNetworkList_support D hdep
  obtain ⟨hdec_univ, _, hsolve, hwid⟩ :=
    projectBucketEliminate_complete_solver f₀ order hsupp hcover hwidth
  refine ⟨?_, ?_, hwid⟩
  · rw [joinConstraint_bucketNetworkList D sep R] at hdec_univ
    exact hdec_univ
  · intro hne
    rw [← joinConstraint_bucketNetworkList D sep R] at hne
    obtain ⟨g, hg, hgf⟩ := hsolve hne
    rw [joinConstraint_bucketNetworkList D sep R, mem_adaptiveSet] at hg
    exact ⟨g, hg, hgf⟩

end STE
