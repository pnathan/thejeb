/-
The elimination fold: running a whole elimination order.

`Ste.Treewidth` bounds a single elimination step (`elimination_step`)
and the total table space of an order (`elimination_order_total_bound`).
This file mechanizes *running* an order: fold conditioning over a list
of `(variable, value)` elimination steps.

Main results:

* `HasSupport.eliminate`: after running an order, the support of the
  constraint is the original support minus the eliminated variables —
  scope accounting for the whole run.
* `mem_eliminate_iff`: elimination is substitution — membership in the
  fully eliminated constraint is membership of the substituted
  assignment in the original one.
* `eliminate_eq_univ_or_empty`: a **complete** order (one whose
  eliminated variables cover a support) decides the constraint: the
  final residue is `univ` or `∅`.
* `condition_eq_self`: conditioning on a variable outside the scope
  does nothing — the algebraic fact that lets bucket elimination touch
  only the bucket of the current variable.

Reference: R. Dechter, *Constraint Processing*, 2003.
-/
import Ste.Treewidth

namespace STE

open Set

variable {V : Type*} {A : V → Type*} [DecidableEq V]

/-! ### Conditioning outside the scope is trivial -/

/-- **Conditioning outside the scope does nothing.**  Fixing a variable
that a constraint does not depend on leaves the constraint unchanged:
bucket elimination may ignore the constraints outside the current
bucket. -/
theorem condition_eq_self {T : Set (∀ v, A v)} {σ : Set V}
    (hT : HasSupport T σ) {v : V} (hv : v ∉ σ) (a : A v) :
    condition T v a = T := by
  ext f
  rw [mem_condition_iff]
  refine hT _ _ fun u hu => ?_
  have huv : u ≠ v := fun h => hv (h ▸ hu)
  exact Function.update_of_ne huv a f

/-! ### The elimination fold -/

/-- Run an elimination order: fold conditioning over a list of
`(variable, value)` elimination steps. -/
def eliminate (order : List ((v : V) × A v)) (T : Set (∀ v, A v)) :
    Set (∀ v, A v) :=
  order.foldl (fun S p => condition S p.1 p.2) T

@[simp] theorem eliminate_nil (T : Set (∀ v, A v)) :
    eliminate [] T = T := rfl

theorem eliminate_cons (p : (v : V) × A v) (order : List ((v : V) × A v))
    (T : Set (∀ v, A v)) :
    eliminate (p :: order) T = eliminate order (condition T p.1 p.2) := rfl

/-- The set of variables an order eliminates. -/
def eliminated (order : List ((v : V) × A v)) : Set V :=
  {u | u ∈ order.map Sigma.fst}

@[simp] theorem eliminated_nil :
    eliminated ([] : List ((v : V) × A v)) = ∅ := by
  ext u
  simp [eliminated]

theorem eliminated_cons (p : (v : V) × A v)
    (order : List ((v : V) × A v)) :
    eliminated (p :: order) = {p.1} ∪ eliminated order := by
  ext u
  simp [eliminated, List.mem_cons]

/-- **Scope accounting for a whole run.**  Running an elimination order
removes every eliminated variable from the support: the residual
constraint lives on `σ \ eliminated order`. -/
theorem HasSupport.eliminate {T : Set (∀ v, A v)} {σ : Set V}
    (hT : HasSupport T σ) (order : List ((v : V) × A v)) :
    HasSupport (STE.eliminate order T) (σ \ eliminated order) := by
  induction order generalizing T σ with
  | nil => simpa using hT
  | cons p order ih =>
      rw [eliminate_cons, eliminated_cons]
      have h := ih (hT.condition p.1 p.2)
      rwa [Set.sdiff_sdiff] at h

/-- **Elimination is substitution.**  An assignment survives the full
elimination fold iff overwriting it with all the eliminated values
satisfies the original constraint. -/
theorem mem_eliminate_iff {T : Set (∀ v, A v)}
    (order : List ((v : V) × A v)) (f : ∀ v, A v) :
    f ∈ eliminate order T
      ↔ order.foldr (fun p g => Function.update g p.1 p.2) f ∈ T := by
  induction order generalizing T with
  | nil => rfl
  | cons p order ih =>
      rw [eliminate_cons, ih, mem_condition_iff]
      rfl

/-- **A complete elimination order decides the constraint.**  If the
order eliminates every variable of a support of `T`, the fully
eliminated constraint is trivial: `univ` (every completion of the
eliminated values succeeds) or `∅` (none does).  Running the order to
the end leaves a decision, not a constraint. -/
theorem eliminate_eq_univ_or_empty {T : Set (∀ v, A v)} {σ : Set V}
    (hT : HasSupport T σ) {order : List ((v : V) × A v)}
    (hcover : σ ⊆ eliminated order) :
    eliminate order T = Set.univ ∨ eliminate order T = ∅ := by
  have h := hT.eliminate order
  rw [Set.sdiff_eq_empty.mpr hcover] at h
  exact (hasSupport_empty_iff _).mp h

end STE
