/-
Conditioning / variable elimination: the algorithmic step.

`Ste.Support` gave constraints a scope; `Ste.Sheaf` showed the diagonal
coupling has no small scope.  This file mechanizes the elimination step
of bucket elimination / variable elimination: *conditioning* a
constraint on fixing
one coordinate `v := a`.

Main results:

* `condition_feasibilitySet`: conditioning commutes with taking the
  feasibility set — one may condition each constraint separately.
* `condition_mono`: conditioning is monotone.
* `HasSupport.condition`: conditioning removes `v` from every scope —
  the eliminated variable disappears from the constraint hypergraph.
* `condition_pi`: conditioning a rectangular constraint on a feasible
  value keeps it rectangular (the eliminated side becomes trivial).
* `condition_diagonal_eq`, `condition_diagonal_rectangular`,
  `condition_diagonal_hasSupport_one`: conditioning the provably
  non-rectangular coupling `diagonal` on either value of variable `0`
  yields a *rectangular* one-variable constraint.  Elimination is
  exactly what dissolves the coupling obstruction: after fixing a cut
  variable, the remaining problem decomposes (cf.
  `feasibilitySet_blockFamily`).

Reference: R. Dechter, "Bucket elimination: a unifying framework for
reasoning," Artificial Intelligence 113 (1999); Freuder, JACM 1982.
-/
import Mathlib.Data.Set.Piecewise
import Ste.Support
import Ste.Sheaf

namespace STE

open Set

variable {V : Type*} {A : V → Type*} {I : Type*} [DecidableEq V]

/-- Conditioning a constraint `T` on the assignment `v := a`: the set of
assignments that satisfy `T` once coordinate `v` is overwritten with
`a`.  This is the substitution step of variable elimination. -/
def condition (T : Set (∀ v, A v)) (v : V) (a : A v) : Set (∀ v, A v) :=
  (fun f => Function.update f v a) ⁻¹' T

theorem mem_condition_iff {T : Set (∀ v, A v)} {v : V} {a : A v}
    {f : ∀ v, A v} :
    f ∈ condition T v a ↔ Function.update f v a ∈ T :=
  Iff.rfl

/-- Conditioning is monotone in the constraint. -/
theorem condition_mono {T U : Set (∀ v, A v)} (h : T ⊆ U) (v : V)
    (a : A v) :
    condition T v a ⊆ condition U v a :=
  Set.preimage_mono h

/-- **Conditioning commutes with feasibility.**  Conditioning the global
feasible set is the feasible set of the conditioned constraints:
variable elimination may be performed constraint-by-constraint. -/
theorem condition_feasibilitySet (S : I → Set (∀ v, A v)) (v : V)
    (a : A v) :
    condition (feasibilitySet S) v a
      = feasibilitySet (fun i => condition (S i) v a) := by
  simp only [condition, feasibilitySet, Set.preimage_iInter]

/-- **Elimination shrinks scopes.**  If `T` is supported on `σ`, the
conditioned constraint is supported on `σ \ {v}`: the eliminated
variable leaves the constraint hypergraph. -/
theorem HasSupport.condition {T : Set (∀ v, A v)} {σ : Set V}
    (hT : HasSupport T σ) (v : V) (a : A v) :
    HasSupport (condition T v a) (σ \ {v}) := by
  intro f g hfg
  refine hT _ _ fun w hw => ?_
  show Function.update f v a w = Function.update g v a w
  by_cases hwv : w = v
  · subst hwv
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hwv, Function.update_of_ne hwv]
    exact hfg w ⟨hw, hwv⟩

/-- **Conditioning a rectangle on a feasible value is a rectangle**: the
`v`-th side becomes trivial and all other sides are untouched.  The
tractable class is closed under variable elimination. -/
theorem condition_pi (P : ∀ v, Set (A v)) {v : V} {a : A v}
    (ha : a ∈ P v) :
    condition (Set.univ.pi P) v a
      = Set.univ.pi (Function.update P v Set.univ) := by
  ext f
  simp only [mem_condition_iff, Set.mem_univ_pi]
  refine forall_congr' fun w => ?_
  by_cases hwv : w = v
  · subst hwv
    simp [Function.update_self, ha]
  · rw [Function.update_of_ne hwv, Function.update_of_ne hwv]

/-! ### Elimination algebra: idempotence and commutation -/

/-- Re-conditioning on an already-eliminated variable is absorbed: the
inner fixed value wins. -/
@[simp]
theorem condition_condition_self (T : Set (∀ v, A v)) (v : V)
    (a b : A v) :
    condition (condition T v a) v b = condition T v a := by
  ext f
  simp only [mem_condition_iff, Function.update_idem]

/-- Conditioning on distinct variables commutes: the elimination order
of distinct variables is immaterial. -/
theorem condition_condition_comm (T : Set (∀ v, A v)) {v w : V}
    (hvw : v ≠ w) (a : A v) (b : A w) :
    condition (condition T v a) w b = condition (condition T w b) v a := by
  ext f
  simp only [mem_condition_iff, Function.update_comm hvw.symm]

/-! ### Block recombination: cut variables disconnect the problem -/

/-- **Feasible sets of block families recombine block-wise.**  If every
constraint has support inside `σ` or inside `σᶜ` (no constraint couples
the two blocks), splicing two feasible assignments along `σ` is again
feasible — the pi-space form of `feasibilitySet_blockFamily`. -/
theorem piecewise_mem_feasibilitySet {S : I → Set (∀ v, A v)}
    {σ : Set V} [∀ u, Decidable (u ∈ σ)]
    (hS : ∀ i, HasSupport (S i) σ ∨ HasSupport (S i) σᶜ)
    {f g : ∀ v, A v} (hf : f ∈ feasibilitySet S)
    (hg : g ∈ feasibilitySet S) :
    σ.piecewise f g ∈ feasibilitySet S := by
  rw [mem_feasibilitySet] at hf hg ⊢
  intro i
  rcases hS i with h | h
  · exact (h f (σ.piecewise f g) fun u hu =>
      (Set.piecewise_eq_of_mem σ f g hu).symm).mp (hf i)
  · exact (h g (σ.piecewise f g) fun u hu =>
      (Set.piecewise_eq_of_notMem σ f g hu).symm).mp (hg i)

/-- **Conditioning on a cut variable splits every scope into a block.**
If each constraint has support inside `σ ∪ {v}` or inside `σᶜ ∪ {v}`
(the blocks talk only through `v`), then after conditioning on `v`
every constraint has support inside a single block. -/
theorem condition_cut_blocks {S : I → Set (∀ v, A v)} {σ : Set V}
    {v : V}
    (hS : ∀ i, HasSupport (S i) (σ ∪ {v}) ∨ HasSupport (S i) (σᶜ ∪ {v}))
    (a : A v) (i : I) :
    HasSupport (condition (S i) v a) σ
      ∨ HasSupport (condition (S i) v a) σᶜ := by
  rcases hS i with h | h
  · refine Or.inl ((h.condition v a).mono fun u hu => ?_)
    rcases hu with ⟨hu1 | hu1, hu2⟩
    · exact hu1
    · exact absurd hu1 hu2
  · refine Or.inr ((h.condition v a).mono fun u hu => ?_)
    rcases hu with ⟨hu1 | hu1, hu2⟩
    · exact hu1
    · exact absurd hu1 hu2

/-- **Eliminating a cut variable disconnects the problem.**  If the
blocks `σ`, `σᶜ` interact only through the cut variable `v`, the
conditioned feasible set is closed under block-wise recombination:
fixing `v := a` splits the residual problem into independent
subproblems on `σ` and `σᶜ`. -/
theorem piecewise_mem_condition_feasibilitySet {S : I → Set (∀ v, A v)}
    {σ : Set V} {v : V} [∀ u, Decidable (u ∈ σ)]
    (hS : ∀ i, HasSupport (S i) (σ ∪ {v}) ∨ HasSupport (S i) (σᶜ ∪ {v}))
    (a : A v) {f g : ∀ v, A v}
    (hf : f ∈ condition (feasibilitySet S) v a)
    (hg : g ∈ condition (feasibilitySet S) v a) :
    σ.piecewise f g ∈ condition (feasibilitySet S) v a := by
  rw [condition_feasibilitySet] at hf hg ⊢
  exact piecewise_mem_feasibilitySet (fun i => condition_cut_blocks hS a i)
    hf hg

/-! ### Eliminating a variable dissolves the coupling core -/

/-- Conditioning the diagonal on `0 := a` leaves the one-variable
constraint `f 1 = a`. -/
theorem condition_diagonal_eq (a : Bool) :
    condition diagonal 0 a = {f | f 1 = a} := by
  ext f
  simp only [mem_condition_iff, diagonal, Set.mem_setOf_eq,
    Function.update_self,
    Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  exact eq_comm

/-- **Variable elimination kills the coupling.**  The diagonal is not
rectangular (`diagonal_not_rectangular`), but conditioning it on either
value of variable `0` IS rectangular.  Fixing a cut variable moves a
constraint from the intractable class to the tractable one. -/
theorem condition_diagonal_rectangular (a : Bool) :
    ∃ t : Fin 2 → Set Bool, condition diagonal 0 a = Set.univ.pi t := by
  refine ⟨fun v => if v = 1 then {a} else Set.univ, ?_⟩
  rw [condition_diagonal_eq]
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_univ_pi]
  constructor
  · intro hf w
    by_cases hw : w = 1
    · subst hw
      simp [hf]
    · simp [hw]
  · intro h
    simpa using h 1

/-- After eliminating variable `0`, the conditioned diagonal has the
singleton support `{1}` — which the diagonal itself provably lacks
(`diagonal_not_hasSupport_one`).  Scope genuinely decreased. -/
theorem condition_diagonal_hasSupport_one (a : Bool) :
    HasSupport (condition diagonal 0 a) ({1} : Set (Fin 2)) := by
  rw [condition_diagonal_eq]
  intro f g hfg
  simp only [Set.mem_setOf_eq, hfg 1 rfl]

end STE
