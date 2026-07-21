/-
Hyperframes: the concept-lattice structure of set theoretic estimation.

Motivation.  In crisp STE one intersects property sets `S i ⊆ Ξ`.  A
recurring worry is *oscillation*: as constraints accumulate, does the
feasible set thrash between empty (over-constrained) and large
(under-constrained)?  The first result here is a disproof of the naive
form: pure accumulation is monotone, so the feasible-set cardinality can
only *decrease*; any increase forces a retraction (constraint deletion).
Oscillation is therefore a phenomenon of the *dynamic* (edit-stream)
regime, not of static STE — it is exactly localized to non-monotone
edits.

The second, structural result identifies the surprising object.  The STE
satisfaction relation `sat S a i := a ∈ S i` is a formal context in the
sense of Formal Concept Analysis (Ganter–Wille), and our
`partialFeasibilitySet S J` is *definitionally* its lower polar.  Hence
the closed feasible sets are the **extents** of a concept lattice
(`Order.Concept`, a `CompleteLattice` in Mathlib), which we name the
**hyperframe** lattice of `S`.  Every hyperframe's extent is the feasible
set of its own constraint signature.

This also fixes the bridges the project has been circling:
* **Rough sets** (Pawlak): `Indisc` below is indiscernibility — two
  hypotheses in exactly the same property sets — an equivalence relation
  whose classes are the resolution floor (no constraint subfamily can
  separate them).
* **Carlson's AEP partition**: the AEP typical set used to *partition the
  work* is such an indiscernibility class; the granularity theorem
  `indisc_mem_iff` is why the partition is STE-invariant.

References: B. Ganter, R. Wille, *Formal Concept Analysis*, 1999;
Z. Pawlak, *Rough Sets*, 1982; Combettes 1993; Carlson 2012.
-/
import Mathlib.Order.Concept
import Mathlib.Data.Set.Card
import Ste.Basic

namespace STE

open Order

variable {Ξ : Type*} {I : Type*} (S : I → Set Ξ)

/-- The STE satisfaction relation / formal context: hypothesis `a`
satisfies constraint `i`. -/
def sat (a : Ξ) (i : I) : Prop := a ∈ S i

/-- Membership in a partial feasibility set is satisfaction of every
enforced constraint. -/
theorem mem_partialFeasibilitySet_iff {J : Set I} {a : Ξ} :
    a ∈ partialFeasibilitySet S J ↔ ∀ i ∈ J, a ∈ S i := by
  simp only [partialFeasibilitySet, Set.mem_iInter]

/-- **The bridge.**  The partial feasibility set of `S` on a constraint
set `J` is exactly the lower polar of the formal context `sat S`.  Thus
STE feasibility *is* Formal Concept Analysis. -/
theorem partialFeasibilitySet_eq_lowerPolar (J : Set I) :
    partialFeasibilitySet S J = lowerPolar (sat S) J := by
  ext a
  rw [mem_partialFeasibilitySet_iff]
  exact ⟨fun h i hi => h i hi, fun h i hi => h hi⟩

/-- A **hyperframe** of a frame family `S` is a formal concept of the STE
context: a Galois-dual pair (feasible set of hypotheses, its constraint
signature).  The hyperframes form a complete lattice. -/
abbrev HyperFrame := Concept Ξ I (sat S)

/-- The hyperframes of `S` form a complete lattice — the surprising
structure organizing all reachable feasible sets. -/
example : CompleteLattice (HyperFrame S) := inferInstance

/-- Every partial feasibility set is an extent of the hyperframe lattice:
the closed feasible sets are exactly the concept extents. -/
theorem isExtent_partialFeasibilitySet (J : Set I) :
    IsExtent (sat S) (partialFeasibilitySet S J) := by
  rw [partialFeasibilitySet_eq_lowerPolar]
  exact isExtent_lowerPolar

/-- Every hyperframe's extent is the feasible set of its own constraint
signature (intent).  The concept lattice is the lattice of
constraint-set / feasible-set fixpoints. -/
theorem hyperFrame_extent_eq_feasibilitySet (c : HyperFrame S) :
    c.extent = partialFeasibilitySet S c.intent := by
  rw [partialFeasibilitySet_eq_lowerPolar, c.lowerPolar_intent]

/-- **Superposition law.**  Enforcing two constraint sets is enforcing
their union: feasibility sets meet under union of constraints. -/
theorem partialFeasibilitySet_union (J K : Set I) :
    partialFeasibilitySet S (J ∪ K)
      = partialFeasibilitySet S J ∩ partialFeasibilitySet S K := by
  ext a
  simp only [mem_partialFeasibilitySet_iff, Set.mem_union, Set.mem_inter_iff]
  exact ⟨fun h => ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩,
         fun h i hi => hi.elim (h.1 i) (h.2 i)⟩

/-! ### No oscillation under accumulation -/

/-- **Cardinality monotonicity.**  Over a finite hypothesis space,
accumulating constraints (a larger enforced set) can only shrink the
feasible set. -/
theorem ncard_partialFeasibilitySet_antitone [Finite Ξ] {J K : Set I}
    (h : J ⊆ K) :
    (partialFeasibilitySet S K).ncard ≤ (partialFeasibilitySet S J).ncard :=
  Set.ncard_le_ncard (partialFeasibilitySet_antitone S h)

/-- **Oscillation requires retraction (disproof of naive oscillation).**
If enforcing `K` yields a strictly larger feasible set than enforcing
`J`, then `K` is *not* a superset of `J`: recovering possibilities forces
dropping (retracting) some constraint.  Hence a monotone accumulation
stream cannot make the feasible cardinality rise — no oscillation without
deletion. -/
theorem lt_ncard_imp_not_subset [Finite Ξ] {J K : Set I}
    (h : (partialFeasibilitySet S J).ncard < (partialFeasibilitySet S K).ncard) :
    ¬ J ⊆ K :=
  fun hJK => absurd (ncard_partialFeasibilitySet_antitone S hJK) (not_le.2 h)

/-! ### Rough-set indiscernibility (Carlson's AEP partition) -/

/-- **Indiscernibility.**  Two hypotheses are indiscernible when they lie
in exactly the same property sets — Pawlak indiscernibility for the STE
context, and the STE reading of an AEP typical-set class. -/
def Indisc (a b : Ξ) : Prop := ∀ i, a ∈ S i ↔ b ∈ S i

/-- Indiscernibility is an equivalence relation; its classes partition
the hypothesis space (the resolution floor). -/
theorem indisc_equivalence : Equivalence (Indisc S) where
  refl _ := fun _ => Iff.rfl
  symm h := fun i => (h i).symm
  trans h₁ h₂ := fun i => (h₁ i).trans (h₂ i)

/-- **Granularity.**  No subfamily of constraints separates indiscernible
hypotheses: they are co-feasible for every enforced constraint set.  This
is why the AEP / indiscernibility partition is STE-invariant. -/
theorem indisc_mem_iff {a b : Ξ} (hab : Indisc S a b) (J : Set I) :
    a ∈ partialFeasibilitySet S J ↔ b ∈ partialFeasibilitySet S J := by
  simp only [mem_partialFeasibilitySet_iff]
  exact ⟨fun h i hi => (hab i).1 (h i hi), fun h i hi => (hab i).2 (h i hi)⟩

end STE
