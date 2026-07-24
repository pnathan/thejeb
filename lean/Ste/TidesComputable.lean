/-
The tides corpus, run through the **computable** STE layer of
`Ste.FiniteInstance`.

`Ste.TidesCorpus` proves the qualitative verdict (empty feasibility set,
minimal cores, dissent structure) by hand-written `Set` arguments.
`Ste.FiniteInstance` proves, once and for all, that for a finite frame
corpus the `Set`-level feasibility question is *equivalent* to the
decidable predicate `Consistent`, and packages the *quantitative*
`disagreementDegree`.

This module fuses the two: it instantiates the general bridge on the
actual tides frames and lets the **Lean kernel compute** the invariants
by `decide` -- the inconsistency verdict, each variable's disagreement
degree, and the set of conflict sites -- rather than asserting them. The
verdict reached here by pure computation (`feasible_eq_empty_computed`)
is the *same statement* as `Ste.TidesCorpus.feasible_eq_empty` proved by
hand, so the computable layer is checked to agree with the verified spec.

Reference: P. L. Combettes, "The Foundations of Set Theoretic
Estimation," Proc. IEEE 81(2), 1993.
-/
import Ste.TidesCorpus
import Ste.FiniteInstance

namespace STE.Tides

open STE

/-! ### The corpus is a frame instance of the general computable layer -/

/-- The by-hand property-set family of `Ste.TidesCorpus` is *definitionally*
the general `frameConstraint` of `Ste.FiniteInstance` applied to the tides
frames -- so every general theorem about `frameConstraint frame`
specializes to this corpus with no glue. -/
theorem constraint_eq_frameConstraint : constraint = frameConstraint frame :=
  rfl

/-! ### The feasibility verdict, computed -/

/-- **The corpus is inconsistent -- decided by the kernel.** Pairwise
compatibility fails (already on `primaryCause`, and on `moonRole`), so
`Consistent frame` reduces to `False`. -/
theorem tides_inconsistent : ¬ Consistent frame := by decide

/-- **The verdict, reached by computation.** Feeding the decided
inconsistency through the general bridge `feasibilitySet_eq_empty_iff`
reproduces `Ste.TidesCorpus.feasible_eq_empty` -- the *same* proposition
`feasibilitySet constraint = ∅`, now obtained from a `by decide` rather
than a hand proof. The computable layer agrees with the verified spec. -/
theorem feasible_eq_empty_computed : feasibilitySet constraint = ∅ := by
  rw [constraint_eq_frameConstraint, feasibilitySet_eq_empty_iff]
  exact tides_inconsistent

/-! ### The quantitative invariants, computed

`disagreementDegree frame v` = the number of distinct values variable `v`
receives across the seven authors. These are the concrete numbers behind
the qualitative story: `moonRole` splits three ways, `mechanism` five, the
unanimous-where-spoken variables sit at degree one. -/

theorem degree_primaryCause : disagreementDegree frame .primaryCause = 3 := by decide
theorem degree_moonRole    : disagreementDegree frame .moonRole    = 3 := by decide
theorem degree_mechanism   : disagreementDegree frame .mechanism   = 5 := by decide
theorem degree_sunRole     : disagreementDegree frame .sunRole     = 2 := by decide
theorem degree_springNeap  : disagreementDegree frame .springNeap  = 1 := by decide
theorem degree_earthMotion : disagreementDegree frame .earthMotion = 1 := by decide
theorem degree_quantitative: disagreementDegree frame .quantitative= 1 := by decide

/-- **`springNeap` is unanimous where spoken** -- degree one, so by the
general characterization every author who mentions it agrees. A positive
structural fact obtained through `agree_iff_degree_le_one`. -/
theorem springNeap_unanimous :
    ∀ a b x y, frame a .springNeap = some x → frame b .springNeap = some y → x = y :=
  agree_iff_degree_le_one.mp (by decide)

/-- The set of **conflict sites**: variables assigned two or more distinct
values. -/
def conflictVars : Finset Var :=
  Finset.univ.filter (fun v => 2 ≤ disagreementDegree frame v)

/-- **Exactly four variables carry the disagreement** -- computed. -/
theorem conflictVars_card : conflictVars.card = 4 := by decide

/-- And they are precisely the four named coupling sites. -/
theorem conflictVars_eq :
    conflictVars = {Var.primaryCause, Var.moonRole, Var.mechanism, Var.sunRole} := by
  decide

/-! ### Executable report

A human-readable dump of the same invariants, produced by running the
computable definitions (not part of the trusted proof). -/

/-- Each variable paired with its computed disagreement degree. -/
def degreeReport : List (Var × ℕ) :=
  [Var.primaryCause, .moonRole, .mechanism, .sunRole,
   .springNeap, .earthMotion, .quantitative].map
    (fun v => (v, disagreementDegree frame v))

-- [(primaryCause, 3), (moonRole, 3), (mechanism, 5), (sunRole, 2),
--  (springNeap, 1), (earthMotion, 1), (quantitative, 1)]
#eval degreeReport
-- false  (the corpus is inconsistent)
#eval decide (Consistent frame)
-- 4  (four conflict sites)
#eval conflictVars.card

end STE.Tides
