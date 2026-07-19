/-
Reduction accounting for STE criteria.

Adding a criterion never enlarges a partial feasible set.  This file reifies the
amount removed as a set of discarded candidates, and separates ordinary
reduction from malformed/incompatible criteria that make feasibility empty.
A numerical or probabilistic score `r` can later estimate the size of these
reduction sets; the order-theoretic facts here do not depend on choosing such a
measure.
-/
import Ste.Algebra

namespace STE

namespace Algebra

variable {Problem Solution Criterion : Type*}

/-- The remaining feasible candidates after adding criterion `c` to an already
enforced criterion set `C`. -/
def remainingAfter (A : Algebra Problem Solution Criterion)
    (p : Problem) (C : Set Criterion) (c : Criterion) : Set Solution :=
  A.partialFeasibleSet p (insert c C)

/-- The candidates removed by adding criterion `c` to an already enforced
criterion set `C`.  This is the exact set-valued reduction; cardinalities,
measures, entropy/AEP estimates, or engineering scores can be layered on top. -/
def reductionSet (A : Algebra Problem Solution Criterion)
    (p : Problem) (C : Set Criterion) (c : Criterion) : Set Solution :=
  A.partialFeasibleSet p C \ A.remainingAfter p C c

/-- Adding a criterion can only shrink the current feasible set. -/
theorem remainingAfter_subset_current (A : Algebra Problem Solution Criterion)
    (p : Problem) (C : Set Criterion) (c : Criterion) :
    A.remainingAfter p C c ⊆ A.partialFeasibleSet p C :=
  A.partialFeasibleSet_antitone p (by
    intro d hd
    exact Set.mem_insert_of_mem c hd)

/-- A reduction set is part of the current feasible set. -/
theorem reductionSet_subset_current (A : Algebra Problem Solution Criterion)
    (p : Problem) (C : Set Criterion) (c : Criterion) :
    A.reductionSet p C c ⊆ A.partialFeasibleSet p C := by
  intro x hx
  exact hx.1

/-- `c` is contradictory relative to the current partial problem if it rejects
every currently feasible candidate. -/
def ContradictsCurrent (A : Algebra Problem Solution Criterion)
    (p : Problem) (C : Set Criterion) (c : Criterion) : Prop :=
  ∀ x, x ∈ A.partialFeasibleSet p C → x ∉ A.propertySet p c

/-- If a new criterion contradicts the current feasible set, adding it leaves no
remaining feasible candidates. -/
theorem remainingAfter_eq_empty_of_contradictsCurrent
    {A : Algebra Problem Solution Criterion} {p : Problem}
    {C : Set Criterion} {c : Criterion}
    (h : A.ContradictsCurrent p C c) : A.remainingAfter p C c = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro x hx
  have hxCurrent : x ∈ A.partialFeasibleSet p C :=
    A.remainingAfter_subset_current p C c hx
  have hxCriterion : x ∈ A.propertySet p c := by
    have hall : ∀ d ∈ insert c C, x ∈ A.propertySet p d :=
      (Algebra.mem_partialFeasibleSet).mp hx
    exact hall c (Set.mem_insert c C)
  exact h x hxCurrent hxCriterion

/-- Two criteria are incompatible on a problem instance if no solution can
satisfy both.  This captures the malformed-constraint case where distinct
property sets are disjoint. -/
def Incompatible (A : Algebra Problem Solution Criterion)
    (p : Problem) (c d : Criterion) : Prop :=
  ∀ x, x ∈ A.propertySet p c → x ∉ A.propertySet p d

/-- Incompatible criteria make the full STE problem unsolvable. -/
theorem not_solvable_of_incompatible
    {A : Algebra Problem Solution Criterion} {p : Problem}
    {c d : Criterion} (h : A.Incompatible p c d) : ¬ A.Solvable p := by
  rintro ⟨x, hx⟩
  have hall : ∀ e, x ∈ A.propertySet p e :=
    (Algebra.mem_feasibleSet).mp hx
  exact h x (hall c) (hall d)

/-- A reduction score is an external estimate of how much a criterion should
shrink the feasible set.  Examples include finite cardinality reduction,
measure loss, entropy/AEP typical-set estimates, or heuristic engineering
priority scores. -/
structure ReductionScore (A : Algebra Problem Solution Criterion)
    (Score : Type*) where
  score : Problem → Criterion → Score

end Algebra

end STE
