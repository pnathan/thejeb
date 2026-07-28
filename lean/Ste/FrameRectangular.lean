/-
Frame corpora are rectangular: the empirical (tides/Federalist) layer
glues over every cover, for free.

`Ste.FiniteInstance` reduces feasibility of a *frame corpus* -- a family
of partial assignments `frame : A → V → Option W`, one author's
Combettes-1993 property set given as the assignments agreeing wherever
`frame a` speaks -- to the decidable, pairwise `Consistent` check
(`nonempty_iff_consistent`).  `Ste.Sheaf` and `Ste.CechCover` separately
establish that *rectangular* constraints (products/cylinders over the
variable set) glue over EVERY cover of the variable set, with no
representation blow-up (`rectangular_feasibilitySet`,
`rectangular_cechVanishesCover`).

This file connects the two.  Every frame corpus is, unconditionally, a
rectangle: a single author's assertion only ever names one value per
variable, so it can never carry the `diagonal`-style coupling that is
the sole obstruction to rectangularity (`Ste.Sheaf.diagonal_not_rectangular`).
Consequently the whole corpus's feasibility set is a rectangle too
(`isRectangle_feasibilitySet_frame`), and the general sheaf theorem for
rectangles applies to it with no further hypotheses
(`frame_cechVanishesCover`).

Together with `nonempty_iff_consistent` this is the "the solver is
justified" theorem of the empirical section of
`papers/papers/ste-cohomology.tex`: the decidable pairwise `Consistent`
check is a complete feasibility test for the tides/Federalist corpus,
AND however the solver partitions the variable set into overlapping
contexts, the local solutions it computes glue to a single global
solution with zero Čech obstruction.  Rectangularity -- not any bespoke
property of tides or Federalist -- is what makes the empirical solver
correct.

Reference: P. L. Combettes, "The Foundations of Set Theoretic
Estimation," Proc. IEEE 81(2), 1993.
-/
import Ste.FiniteInstance
import Ste.RepresentationBounds
import Ste.CechCover
import Ste.SupportCover

namespace STE

open Set

variable {A V W : Type*}

/-! ### A frame corpus is a rectangle -/

/-- The per-variable side of the rectangle representing one author's
constraint: the singleton `{x}` where `frame a v = some x` (the author
speaks), and `univ` (no constraint at all) where the author is silent. -/
def frameConstraintSide (frame : A → V → Option W) (a : A) (v : V) :
    Set W :=
  match frame a v with
  | some x => {x}
  | none => Set.univ

/-- **A single author's constraint is exactly a rectangle.**  This is
the set-level content behind `frameConstraint_isRectangle`: the property
set of a partial assignment is the product, over the variables, of a
singleton (where the author speaks) or the whole value space (where the
author is silent) -- never a genuine cross-variable coupling. -/
theorem frameConstraint_eq_pi (frame : A → V → Option W) (a : A) :
    frameConstraint frame a
      = Set.univ.pi (fun v : V => frameConstraintSide frame a v) := by
  ext f
  simp only [mem_frameConstraint, Set.mem_univ_pi]
  constructor
  · intro h v
    rcases hv : frame a v with _ | x
    · simp [frameConstraintSide, hv]
    · have hx := h v x hv
      simp [frameConstraintSide, hv, hx]
  · intro h v x hx
    have hv := h v
    simp only [frameConstraintSide, hx] at hv
    exact hv

/-- **Discharges part 1 of the "solver is justified" claim of
`papers/papers/ste-cohomology.tex`:** every author's property set in a
frame corpus is a rectangle (Combettes 1993 property set, variable-
separable by construction of `frameConstraint`).  A single piece of
frame evidence never couples two variables, so it carries none of the
`diagonal_not_rectangular` (`Ste.Sheaf`) obstruction. -/
theorem frameConstraint_isRectangle (frame : A → V → Option W) (a : A) :
    IsRectangle (A := fun _ : V => W) (frameConstraint frame a) :=
  ⟨frameConstraintSide frame a, frameConstraint_eq_pi frame a⟩

/-- **Discharges part 2 of the "solver is justified" claim of
`papers/papers/ste-cohomology.tex`:** the whole feasibility set of a
frame corpus -- the intersection of every author's rectangle -- is
again a rectangle, with side `⋂ a, frameConstraintSide frame a v` at
each variable `v`.  Follows `frameConstraint_isRectangle` by
`rectangular_feasibilitySet` (`Ste.Sheaf`): intersections of rectangles
sharing a common index space are rectangles. -/
theorem isRectangle_feasibilitySet_frame (frame : A → V → Option W) :
    IsRectangle (A := fun _ : V => W)
      (feasibilitySet (frameConstraint frame)) := by
  refine ⟨fun v => ⋂ a, frameConstraintSide frame a v, ?_⟩
  have heq : frameConstraint frame
      = fun a => Set.univ.pi (fun v => frameConstraintSide frame a v) :=
    funext (frameConstraint_eq_pi frame)
  rw [heq]
  exact rectangular_feasibilitySet _

/-! ### Frame corpora glue over every cover -/

/-- **Discharges part 3 (the headline) of the "solver is justified"
claim of `papers/papers/ste-cohomology.tex`:** for ANY cover
`U : J → Set V` of the variable set, the Čech obstruction of a frame
corpus's feasibility set vanishes -- every compatible family of local
sections (e.g. independent solver runs on the contexts `U j`) glues to
a single global solution, with no representation blow-up
(`rectangular_cechVanishesCover`, `Ste.CechCover`).  Together with
`nonempty_iff_consistent` (`Ste.FiniteInstance`) this completes the
justification of the empirical (tides/Federalist) solver: the decidable
pairwise `Consistent` check is a complete feasibility test, and however
the solver partitions the variables into overlapping contexts its local
answers glue to a global one automatically -- rectangularity, not any
bespoke property of the corpus, makes this so. -/
theorem frame_cechVanishesCover {J : Type*} (frame : A → V → Option W)
    (U : J → Set V) (hcover : ∀ v, ∃ j, v ∈ U j) :
    CechVanishesCover (feasibilitySet (frameConstraint frame)) U :=
  cechVanishesCover_of_rectangular (isRectangle_feasibilitySet_frame frame)
    U hcover

/-! ### The unary-generator decomposition -/

/-- The single-variable cell cut out by author `a`'s assertion at `v`:
the assignments agreeing with `a` at `v` (vacuously all of `V → W` if
`a` is silent there). -/
def frameCell (frame : A → V → Option W) (a : A) (v : V) : Set (V → W) :=
  {f | ∀ x, frame a v = some x → f v = x}

/-- **The unary-generator form of a frame corpus.**  Each author's
constraint is exactly the intersection of its own single-variable
cells, one cell per variable -- the scoped generating family that feeds
`cechVanishesCover_of_refiningGenerators` (`Ste.SupportCover`) directly,
without going through the rectangle detour. -/
theorem frameConstraint_eq_iInter_frameCell (frame : A → V → Option W)
    (a : A) : frameConstraint frame a = ⋂ v, frameCell frame a v := by
  ext f
  simp only [mem_frameConstraint, Set.mem_iInter, frameCell, Set.mem_setOf_eq]

/-- **Each single-variable cell has support exactly `{v}`:** whether an
assignment belongs depends only on its value at `v`.  This is the
`HasSupport` witness that makes `frameCell` a legitimate scoped
generator for `cechVanishesCover_of_refiningGenerators`. -/
theorem hasSupport_frameCell (frame : A → V → Option W) (a : A) (v : V) :
    HasSupport (frameCell frame a v) ({v} : Set V) := by
  intro f g hfg
  have hv : f v = g v := hfg v (Set.mem_singleton_iff.mpr rfl)
  simp only [frameCell, Set.mem_setOf_eq, hv]

end STE
