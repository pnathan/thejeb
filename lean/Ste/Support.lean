/-
Support (scope) of a constraint on a product hypothesis space.

`Ste.Sheaf` located tractability in variable-separability: rectangular
constraints have linear-size representations, coupling constraints
(`diagonal`) provably do not.  This file introduces the *support* of a
constraint — the set of variables its membership actually depends on —
which is the hypergraph-edge notion underlying treewidth-style
decompositions: a constraint with support `σ` is an edge on `σ`, and the
block structure of `Ste.Decomposition` is exactly disjointness of
supports.

Main notions and results:

* `HasSupport T σ`: membership in `T` depends only on the coordinates in
  `σ`.
* `HasSupport.mono`: any superset of a support is a support.
* `hasSupport_empty_iff`: support `∅` means the constraint is trivial
  (`univ` or `∅`) — a constraint with no scope carries no information.
* `hasSupport_pi`: a cylinder `univ.pi P` is supported on any `σ`
  containing its non-trivial coordinates `{v | P v ≠ univ}`.
* `HasSupport.inter`, `hasSupport_feasibilitySet`: supports are stable
  under intersection, so the feasible set of a family supported on `σ`
  is supported on `σ`.

Reference: R. Dechter, *Constraint Processing*, 2003 (scopes of
constraints); Freuder, JACM 1982.
-/
import Ste.Basic
import Ste.Sheaf

namespace STE

open Set

variable {V : Type*} {A : V → Type*} {I : Type*}

/-- A constraint `T` on the product space `∀ v, A v` *has support* `σ`
when membership in `T` depends only on the coordinates in `σ`: any two
assignments agreeing on `σ` are both in or both out of `T`. -/
def HasSupport (T : Set (∀ v, A v)) (σ : Set V) : Prop :=
  ∀ f g : ∀ v, A v, (∀ v ∈ σ, f v = g v) → (f ∈ T ↔ g ∈ T)

/-- Every constraint is supported on all variables. -/
theorem hasSupport_univ (T : Set (∀ v, A v)) :
    HasSupport T Set.univ := by
  intro f g hfg
  have : f = g := funext fun v => hfg v (Set.mem_univ v)
  rw [this]

/-- **Support is monotone**: any superset of a support is a support. -/
theorem HasSupport.mono {T : Set (∀ v, A v)} {σ σ' : Set V}
    (hσ : σ ⊆ σ') (h : HasSupport T σ) : HasSupport T σ' :=
  fun f g hfg => h f g fun v hv => hfg v (hσ hv)

/-- **Empty support means trivial**: a constraint whose membership
depends on no variable is `univ` or `∅` — scope-free information is no
information. -/
theorem hasSupport_empty_iff (T : Set (∀ v, A v)) :
    HasSupport T (∅ : Set V) ↔ T = Set.univ ∨ T = ∅ := by
  constructor
  · intro h
    rcases eq_empty_or_nonempty T with hT | ⟨f, hf⟩
    · exact Or.inr hT
    · refine Or.inl (Set.eq_univ_of_forall fun g => ?_)
      exact (h f g fun v hv => absurd hv (Set.notMem_empty v)).mp hf
  · rintro (rfl | rfl) <;> intro f g _ <;> simp

/-- The whole space and the empty constraint are supported anywhere,
in particular on `∅`. -/
theorem hasSupport_empty_of_univ :
    HasSupport (Set.univ : Set (∀ v, A v)) (∅ : Set V) :=
  (hasSupport_empty_iff _).mpr (Or.inl rfl)

/-- **Cylinders are supported on their non-trivial coordinates.**  A
rectangular constraint `univ.pi P` has support any `σ` containing every
coordinate where `P` genuinely constrains (`P v ≠ univ`). -/
theorem hasSupport_pi (P : ∀ v, Set (A v)) {σ : Set V}
    (hP : {v | P v ≠ Set.univ} ⊆ σ) :
    HasSupport (Set.univ.pi P) σ := by
  intro f g hfg
  simp only [Set.mem_univ_pi]
  refine forall_congr' fun v => ?_
  by_cases hv : v ∈ σ
  · rw [hfg v hv]
  · have htriv : P v = Set.univ := by
      by_contra hne
      exact hv (hP hne)
    rw [htriv]
    simp

/-- Supports are stable under intersection. -/
theorem HasSupport.inter {T U : Set (∀ v, A v)} {σ : Set V}
    (hT : HasSupport T σ) (hU : HasSupport U σ) :
    HasSupport (T ∩ U) σ := by
  intro f g hfg
  rw [Set.mem_inter_iff, Set.mem_inter_iff, hT f g hfg, hU f g hfg]

/-- **The feasible set inherits the common support**: if every property
set of an STE problem is supported on `σ`, so is the feasibility set.
Constraint scopes bound the scope of the aggregate. -/
theorem hasSupport_feasibilitySet {S : I → Set (∀ v, A v)} {σ : Set V}
    (hS : ∀ i, HasSupport (S i) σ) :
    HasSupport (feasibilitySet S) σ := by
  intro f g hfg
  simp only [mem_feasibilitySet]
  exact forall_congr' fun i => hS i f g hfg

/-! ### The coupling core has no small support -/

/-- **The diagonal is genuinely two-variable**: every support of the
coupling constraint `diagonal` contains both variables.  Its scope
cannot be shrunk below `{0, 1}` — the irreducible coupling core behind
`diagonal_not_rectangular`. -/
theorem diagonal_support_full {σ : Set (Fin 2)}
    (h : HasSupport diagonal σ) :
    (0 : Fin 2) ∈ σ ∧ (1 : Fin 2) ∈ σ := by
  constructor
  · by_contra h0
    have hagree : ∀ v ∈ σ,
        (fun _ : Fin 2 => false) v = (fun v : Fin 2 => decide (v = 0)) v := by
      intro v hv
      have hv0 : v ≠ 0 := fun e => h0 (e ▸ hv)
      simp [hv0]
    exact absurd
      (show decide ((0 : Fin 2) = 0) = decide ((1 : Fin 2) = 0) from
        (h _ _ hagree).mp rfl)
      (by decide)
  · by_contra h1
    have hagree : ∀ v ∈ σ,
        (fun _ : Fin 2 => false) v = (fun v : Fin 2 => decide (v = 1)) v := by
      intro v hv
      have hv1 : v ≠ 1 := fun e => h1 (e ▸ hv)
      simp [hv1]
    exact absurd
      (show decide ((0 : Fin 2) = 1) = decide ((1 : Fin 2) = 1) from
        (h _ _ hagree).mp rfl)
      (by decide)

/-- The diagonal has no empty support: it is not a trivial constraint. -/
theorem diagonal_not_hasSupport_empty :
    ¬ HasSupport diagonal (∅ : Set (Fin 2)) :=
  fun h => Set.notMem_empty _ (diagonal_support_full h).1

/-- The diagonal is not a constraint on variable `0` alone. -/
theorem diagonal_not_hasSupport_zero :
    ¬ HasSupport diagonal ({0} : Set (Fin 2)) :=
  fun h =>
    absurd (Set.mem_singleton_iff.mp (diagonal_support_full h).2) (by decide)

/-- The diagonal is not a constraint on variable `1` alone. -/
theorem diagonal_not_hasSupport_one :
    ¬ HasSupport diagonal ({1} : Set (Fin 2)) :=
  fun h =>
    absurd (Set.mem_singleton_iff.mp (diagonal_support_full h).1) (by decide)

/-- Conversely the diagonal is supported on `{0, 1}`; with
`diagonal_support_full` this identifies its scope exactly. -/
theorem diagonal_hasSupport_pair :
    HasSupport diagonal ({0, 1} : Set (Fin 2)) := by
  intro f g hfg
  have h0 := hfg 0 (Set.mem_insert _ _)
  have h1 := hfg 1 (Set.mem_insert_of_mem _ rfl)
  simp only [diagonal, Set.mem_setOf_eq, h0, h1]

end STE
