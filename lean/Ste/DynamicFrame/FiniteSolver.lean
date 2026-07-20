/-
Executable finite representation and quantitative limits for the exact STE
solver.

When the ambient hypothesis type is finite and satisfaction is decidable, a
solver state is represented exactly by a `Finset`.  Filtering implements
property-set intersection.  The representation stores at most N worlds, where
N is the cardinality of the ambient exact universe, and a complete state space
contains exactly 2^N possible states.  The latter bound is also an
impossibility result: unrestricted crisp property sets can select an arbitrary
subset, so no smaller uniform family of extensional states can be complete.
-/
import Ste.DynamicFrame.Solver
import Mathlib.Data.Finset.Powerset

namespace STE.DynamicFrame

universe uDoc uClaim uFrame uHypothesis uConstraint

namespace Model

variable {Document : Type uDoc} {Claim : Type uClaim} {Frame : Type uFrame}
variable {Hypothesis : Type uHypothesis} {Constraint : Type uConstraint}
variable (M : Model Document Claim Frame Hypothesis Constraint)

section Finite

variable [Fintype Hypothesis] [DecidableEq Hypothesis]
variable [∀ h k, Decidable (M.satisfies h k)]

/-- One exact finite property-set application. -/
def applyFinite (X : Finset Hypothesis) (k : Constraint) : Finset Hypothesis :=
  X.filter (fun h => M.satisfies h k)

@[simp] theorem mem_applyFinite {X : Finset Hypothesis} {k : Constraint}
    {h : Hypothesis} :
    h ∈ M.applyFinite X k ↔ h ∈ X ∧ M.satisfies h k := by
  simp [applyFinite]

/-- The finite implementation denotes exactly the set implementation. -/
theorem coe_applyFinite (X : Finset Hypothesis) (k : Constraint) :
    (M.applyFinite X k : Set Hypothesis) =
      M.applyConstraint (X : Set Hypothesis) k := by
  ext h
  simp [applyFinite, applyConstraint, propertySet]

/-- Executable repeated filtering. -/
def runFinite : List Constraint → Finset Hypothesis → Finset Hypothesis
  | [], X => X
  | k :: ks, X => M.runFinite ks (M.applyFinite X k)

/-- Start the executable solver from the complete finite universe. -/
def solveFinite (ks : List Constraint) : Finset Hypothesis :=
  M.runFinite ks Finset.univ

/-- Finite execution is extensionally identical to the abstract STE run. -/
theorem coe_runFinite (ks : List Constraint) (X : Finset Hypothesis) :
    (M.runFinite ks X : Set Hypothesis) = M.run ks (X : Set Hypothesis) := by
  induction ks generalizing X with
  | nil => rfl
  | cons k ks ih =>
      rw [runFinite, M.run, ih, M.coe_applyFinite]

/-- Consequently the executable output is exactly partial feasibility. -/
theorem coe_solveFinite (ks : List Constraint) :
    (M.solveFinite ks : Set Hypothesis) = M.solve ks := by
  rw [solveFinite, M.coe_runFinite, solve]
  apply congrArg (M.run ks)
  ext h
  simp

theorem applyFinite_subset (X : Finset Hypothesis) (k : Constraint) :
    M.applyFinite X k ⊆ X :=
  Finset.filter_subset _ _

theorem applyFinite_card_le (X : Finset Hypothesis) (k : Constraint) :
    (M.applyFinite X k).card ≤ X.card :=
  Finset.card_le_card (M.applyFinite_subset X k)

/-- A nontrivial property-set application removes at least one exact world. -/
theorem applyFinite_card_lt {X : Finset Hypothesis} {k : Constraint}
    (hne : M.applyFinite X k ≠ X) :
    (M.applyFinite X k).card < X.card := by
  apply Finset.card_lt_card
  refine ⟨M.applyFinite_subset X k, ?_⟩
  intro hback
  apply hne
  exact Finset.Subset.antisymm (M.applyFinite_subset X k) hback

/-- The exact number of worlds eliminated by a finite schedule. -/
def reductionCost (ks : List Constraint) (X : Finset Hypothesis) : Nat :=
  X.card - (M.runFinite ks X).card

/-- Ambient cardinality N: the unconditional storage and query-scan bound. -/
include M in
def maxWorlds : Nat := Fintype.card Hypothesis

/-- Total reduction is at most N.  In particular, a schedule can contain at
most N steps that each remove a previously surviving world. -/
theorem reductionCost_le_maxWorlds (ks : List Constraint)
    (X : Finset Hypothesis) :
    M.reductionCost ks X ≤ M.maxWorlds := by
  calc
    M.reductionCost ks X ≤ X.card := Nat.sub_le _ _
    _ ≤ (Finset.univ : Finset Hypothesis).card :=
      Finset.card_le_card (Finset.subset_univ X)
    _ = M.maxWorlds := by simp [maxWorlds]

/-- Every possible extensional exact solver state. -/
include M in
def allExactStates : Finset (Finset Hypothesis) :=
  (Finset.univ : Finset Hypothesis).powerset

theorem mem_allExactStates (X : Finset Hypothesis) :
    X ∈ (M.allExactStates : Finset (Finset Hypothesis)) := by
  simp [allExactStates]

/-- There are exactly 2^N extensional states over N ambient worlds. -/
theorem card_allExactStates :
    (M.allExactStates : Finset (Finset Hypothesis)).card =
      2 ^ M.maxWorlds := by
  simp [allExactStates, maxWorlds]

end Finite

end Model

/-- Crisp STE has full subset expressivity: one property set can select any
chosen subset of the ambient universe.  Together with `card_allExactStates`,
this proves that the 2^N bound cannot be reduced without structural assumptions
on the generated property sets. -/
theorem arbitrary_subset_as_single_property {Hypothesis : Type*}
    (A : Set Hypothesis) :
    partialFeasibilitySet (fun _ : Unit => A) Set.univ = A := by
  ext h
  simp [partialFeasibilitySet]

end STE.DynamicFrame
