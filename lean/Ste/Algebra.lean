/-
Abstract algebra of STE problems.

A crisp STE algebra is a meet construction in the powerset lattice of candidate
solutions.  For each problem instance, each criterion denotes a property set of
solutions, and solving means taking the meet (intersection) of all those
property sets.  Nonempty meet is solvability; singleton meet is identification.
-/
import Ste.Basic

namespace STE

variable {Problem Solution Criterion : Type*}

/-- An abstract crisp STE algebra: every problem instance and criterion determine
one property set of admissible solutions.  The algebraic operation that solves a
problem is meet/intersection in the powerset lattice of `Solution`. -/
structure Algebra (Problem Solution Criterion : Type*) where
  propertySet : Problem → Criterion → Set Solution

/-- The property-set family attached to a problem instance. -/
def Algebra.criteria (A : Algebra Problem Solution Criterion) (p : Problem) :
    Criterion → Set Solution :=
  A.propertySet p

/-- The feasible solutions of a problem instance: the meet of all criteria. -/
def Algebra.feasibleSet (A : Algebra Problem Solution Criterion) (p : Problem) :
    Set Solution :=
  STE.feasibilitySet (A.criteria p)

@[simp] theorem Algebra.mem_feasibleSet {A : Algebra Problem Solution Criterion}
    {p : Problem} {x : Solution} :
    x ∈ A.feasibleSet p ↔ ∀ c, x ∈ A.propertySet p c :=
  STE.mem_feasibilitySet

/-- A candidate solves an instance when it lies in the meet of all criteria. -/
def Algebra.Solves (A : Algebra Problem Solution Criterion)
    (p : Problem) (x : Solution) : Prop :=
  x ∈ A.feasibleSet p

/-- A problem instance is STE-solvable when the criterion meet is nonempty. -/
def Algebra.Solvable (A : Algebra Problem Solution Criterion) (p : Problem) :
    Prop :=
  (A.feasibleSet p).Nonempty

/-- A property-family is sound/fair for a proposed true solution when every
criterion contains that solution. -/
def Algebra.SoundFor (A : Algebra Problem Solution Criterion)
    (p : Problem) (x : Solution) : Prop :=
  STE.Fair (A.criteria p) x

/-- A problem instance is identified by `x` when its criterion meet is exactly
that singleton. -/
def Algebra.Identifies (A : Algebra Problem Solution Criterion)
    (p : Problem) (x : Solution) : Prop :=
  STE.Ideal (A.criteria p) x

/-- Sound criteria make a problem instance solvable. -/
theorem Algebra.solvable_of_soundFor {A : Algebra Problem Solution Criterion}
    {p : Problem} {x : Solution} (h : A.SoundFor p x) : A.Solvable p :=
  STE.feasibilitySet_nonempty_of_fair h

/-- If the criteria identify `x`, every feasible solution is `x`. -/
theorem Algebra.eq_of_identifies {A : Algebra Problem Solution Criterion}
    {p : Problem} {x y : Solution} (h : A.Identifies p x)
    (hy : A.Solves p y) : y = x :=
  STE.Ideal.eq_of_mem h hy

/-- Restricting attention to some criteria gives a partial meet. -/
def Algebra.partialFeasibleSet (A : Algebra Problem Solution Criterion)
    (p : Problem) (C : Set Criterion) : Set Solution :=
  STE.partialFeasibilitySet (A.criteria p) C

@[simp] theorem Algebra.mem_partialFeasibleSet
    {A : Algebra Problem Solution Criterion} {p : Problem}
    {C : Set Criterion} {x : Solution} :
    x ∈ A.partialFeasibleSet p C ↔ ∀ c ∈ C, x ∈ A.propertySet p c := by
  simp [Algebra.partialFeasibleSet, STE.partialFeasibilitySet, Algebra.criteria]

/-- Adding criteria is antitone: more criteria can only shrink the solution set. -/
theorem Algebra.partialFeasibleSet_antitone
    (A : Algebra Problem Solution Criterion) (p : Problem)
    {C D : Set Criterion} (hCD : C ⊆ D) :
    A.partialFeasibleSet p D ⊆ A.partialFeasibleSet p C :=
  STE.partialFeasibilitySet_antitone (A.criteria p) hCD

/-- An abstract STE algebra is equivalently just its curried interpretation map
from problem instances and criteria into the powerset lattice of solutions. -/
def algebraEquivProperties :
    Algebra Problem Solution Criterion ≃
      (Problem → Criterion → Set Solution) where
  toFun := fun A => A.propertySet
  invFun := fun S => ⟨S⟩
  left_inv := by
    intro A
    cases A
    rfl
  right_inv := by
    intro S
    rfl

end STE
