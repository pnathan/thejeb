/-
Convex set theoretic estimation.

Reference:
  P. L. Combettes, "The Foundations of Set Theoretic Estimation,"
  Proc. IEEE 81(2):182-208, 1993, §III-IV: in the classical signal
  processing instantiation the solution space is a (real) Hilbert space
  and the property sets are closed convex sets, so that the feasibility
  set is closed convex and POCS-type projection algorithms apply.

Here we record the purely convex-geometric part: convexity of the
feasibility set.  (The projection algorithms themselves are future
work; Mathlib has the requisite `Mathlib.Analysis.InnerProductSpace`
projection machinery.)
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Basic
import Ste.Basic

namespace STE

variable {E : Type*} {I : Type*} [AddCommMonoid E] [Module ℝ E]

/-- If every property set is convex, the feasibility set is convex
(Combettes 1993, §III: the intersection of the convex constraints is
the convex feasibility set). -/
theorem convex_feasibilitySet {S : I → Set E} (hc : ∀ i, Convex ℝ (S i)) :
    Convex ℝ (feasibilitySet S) :=
  convex_iInter hc

/-- Partial feasibility sets of convex constraints are convex, for any
enforced subfamily of the information. -/
theorem convex_partialFeasibilitySet {S : I → Set E}
    (hc : ∀ i, Convex ℝ (S i)) (J : Set I) :
    Convex ℝ (partialFeasibilitySet S J) :=
  convex_iInter₂ fun i _ => hc i

end STE
