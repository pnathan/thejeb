/-
An STE solver for dynamic frame normalization.

There is no extra semantic layer hidden behind the word "solver": its state is
a set of exact normalization hypotheses, applying a constraint is intersection
with that constraint's property set, and reduction is the part of the state
discarded by that intersection.  A finite run is repeated property-set
application and is extensionally the corresponding partial feasibility set.
-/
import Ste.DynamicFrame.Laws

namespace STE.DynamicFrame

universe uDoc uClaim uFrame uHypothesis uConstraint

namespace Model

variable {Document : Type uDoc} {Claim : Type uClaim} {Frame : Type uFrame}
variable {Hypothesis : Type uHypothesis} {Constraint : Type uConstraint}
variable (M : Model Document Claim Frame Hypothesis Constraint)

/-- Apply one STE property set to the current solver state. -/
def applyConstraint (X : Set Hypothesis) (k : Constraint) : Set Hypothesis :=
  X ∩ M.propertySet k

/-- Exact set-valued reduction caused by one property-set application. -/
def solverReduction (X : Set Hypothesis) (k : Constraint) : Set Hypothesis :=
  X \ M.applyConstraint X k

/-- Repeated property-set application. -/
def run : List Constraint → Set Hypothesis → Set Hypothesis
  | [], X => X
  | k :: ks, X => M.run ks (M.applyConstraint X k)

/-- Solve a finite constraint presentation from the full hypothesis universe. -/
def solve (ks : List Constraint) : Set Hypothesis :=
  M.run ks Set.univ

@[simp] theorem mem_applyConstraint {X : Set Hypothesis} {k : Constraint}
    {h : Hypothesis} :
    h ∈ M.applyConstraint X k ↔ h ∈ X ∧ M.satisfies h k :=
  Iff.rfl

theorem applyConstraint_subset (X : Set Hypothesis) (k : Constraint) :
    M.applyConstraint X k ⊆ X :=
  Set.inter_subset_left

/-- Applying a constraint is idempotent. -/
theorem applyConstraint_idempotent (X : Set Hypothesis) (k : Constraint) :
    M.applyConstraint (M.applyConstraint X k) k =
      M.applyConstraint X k := by
  ext h
  simp [applyConstraint, propertySet, and_assoc]

/-- Property-set applications commute. -/
theorem applyConstraint_comm (X : Set Hypothesis) (k l : Constraint) :
    M.applyConstraint (M.applyConstraint X k) l =
      M.applyConstraint (M.applyConstraint X l) k := by
  ext h
  simp [applyConstraint, propertySet, and_left_comm, and_assoc]

/-- Reduction is exactly the current candidates that violate the new
constraint. -/
theorem mem_solverReduction {X : Set Hypothesis} {k : Constraint}
    {h : Hypothesis} :
    h ∈ M.solverReduction X k ↔ h ∈ X ∧ ¬M.satisfies h k := by
  simp [solverReduction, applyConstraint, propertySet]

/-- The current state decomposes into survivors and the exact reduction set. -/
theorem apply_union_reduction (X : Set Hypothesis) (k : Constraint) :
    M.applyConstraint X k ∪ M.solverReduction X k = X := by
  ext h
  by_cases hk : M.satisfies h k <;>
    simp [applyConstraint, solverReduction, propertySet, hk]

/-- A property set causes no reduction exactly when every current candidate
already satisfies it. -/
theorem solverReduction_eq_empty_iff (X : Set Hypothesis) (k : Constraint) :
    M.solverReduction X k = ∅ ↔ X ⊆ M.propertySet k := by
  rw [solverReduction, Set.diff_eq_empty]
  constructor
  · intro hX h hh
    exact (hX hh).2
  · intro hX h hh
    exact ⟨hh, hX hh⟩

/-- Membership after a run is membership in the initial state plus satisfaction
of every applied property set. -/
theorem mem_run (ks : List Constraint) (X : Set Hypothesis) (h : Hypothesis) :
    h ∈ M.run ks X ↔ h ∈ X ∧ ∀ k ∈ ks, M.satisfies h k := by
  induction ks generalizing X with
  | nil => simp [run]
  | cons k ks ih =>
      simp [run, ih, applyConstraint, propertySet, and_assoc]

/-- A finite run is exactly intersection with the partial STE feasibility set
denoted by the constraints in the list. -/
theorem run_eq_inter_partial (ks : List Constraint) (X : Set Hypothesis) :
    M.run ks X =
      X ∩ partialFeasibilitySet M.propertySet {k | k ∈ ks} := by
  ext h
  rw [M.mem_run]
  simp [partialFeasibilitySet, propertySet]

/-- Solving is literally partial STE feasibility. -/
theorem solve_eq_partialFeasibilitySet (ks : List Constraint) :
    M.solve ks = partialFeasibilitySet M.propertySet {k | k ∈ ks} := by
  rw [solve, M.run_eq_inter_partial]
  simp

/-- Solver output depends only on which property sets were applied, not their
order or multiplicity. -/
theorem solve_congr {ks ls : List Constraint}
    (hmem : ∀ k, k ∈ ks ↔ k ∈ ls) :
    M.solve ks = M.solve ls := by
  rw [M.solve_eq_partialFeasibilitySet, M.solve_eq_partialFeasibilitySet]
  have hset : {k : Constraint | k ∈ ks} = {k : Constraint | k ∈ ls} := by
    ext k
    exact hmem k
  rw [hset]

/-- A permutation of the application schedule leaves the result unchanged. -/
theorem solve_perm {ks ls : List Constraint} (hp : ks.Perm ls) :
    M.solve ks = M.solve ls :=
  M.solve_congr (fun k => hp.mem_iff)

/-- If a finite list enumerates exactly the active provenance-indexed
constraints, the operational solver output is the model's feasible set. -/
theorem solve_eq_feasible {D : Set Document} {ks : List Constraint}
    (hactive : ∀ k, k ∈ ks ↔ k ∈ M.activeConstraints D) :
    M.solve ks = M.feasible D := by
  ext h
  rw [M.solve_eq_partialFeasibilitySet]
  simp only [partialFeasibilitySet, Set.mem_iInter, Set.mem_setOf_eq,
    propertySet, feasible]
  constructor
  · intro hh k hk
    exact hh k ((hactive k).mpr hk)
  · intro hh k hk
    exact hh k ((hactive k).mp hk)

end Model

end STE.DynamicFrame
