/-
The set-valued frame: the semantic primitive underneath `Ste.HyperFrame`.

`Ste.FiniteInstance` fixes each source's information as a *crisp* partial
assignment `frame a : V → Option W`, one value per variable or silence.
That is a special case of something more basic: a source's information
about a variable `v` need not be a single value at all, only a
*possibility set* `F v ⊆ A v` -- the values the source has not ruled out.
This file makes that possibility-set frame explicit, in STE vocabulary,
as `SetValuedFrame`, and reduces its theory to results already proved
elsewhere:

* `propertySet_isRectangle` -- a set-valued frame's induced property set
  (Combettes 1993, §II-C) is by construction the box `univ.pi F`, so it
  is trivially a rectangle (`Ste.RepresentationBounds.IsRectangle`).
* `corpusFeasibilitySet_cechVanishesCover` -- a *corpus* of set-valued
  frames (one per source `i : I`) therefore has vanishing Čech
  obstruction over EVERY cover of the variable set
  (`Ste.CechCover.cechVanishesCover_of_rectangular`), generalizing
  `Ste.FrameRectangular.frame_cechVanishesCover` from crisp to
  set-valued frames -- no new gluing argument is needed, only the
  rectangle fact.
* `corpusFeasibilitySet_nonempty_iff` -- feasibility of the corpus is
  EXACTLY a per-variable test: a common point in `⋂ i, F i v` at every
  `v`. This is the set-valued generalization of
  `Ste.FiniteInstance.consistent_iff_forall_disagreementDegree_le_one`
  (there: disagreement degree ≤ 1 per variable; here: nonempty
  intersection of possibility sets per variable).
* `ofCrisp` / `propertySet_ofCrisp` -- the crisp frame of
  `Ste.FiniteInstance` is recovered exactly as the special case of a
  `SetValuedFrame` whose sides are singletons (where the source speaks)
  or the whole space (where it is silent) -- literally
  `Ste.FrameRectangular.frameConstraintSide` read in this vocabulary.
  `hasHelly_ofCrisp_two` transports `Ste.HellyConsistency.frame_hasHelly_two`
  along that agreement: in the crisp special case pairwise per-variable
  compatibility already certifies global feasibility, but (per the
  remark after `corpusFeasibilitySet_nonempty_iff`) this Helly-2 property
  is special to the crisp case and does not hold for set-valued frames
  in general.

Reference: P. L. Combettes, "The Foundations of Set Theoretic
Estimation," Proc. IEEE 81(2), 1993.
-/
import Ste.FrameRectangular
import Ste.HellyConsistency
import Ste.HyperFrame
import Ste.Sheaf
import Ste.CechCover

namespace STE

open Set

/-! ### The set-valued frame -/

/-- A **set-valued frame** (possibility-set frame): one source's
assignment of a *possibility set* `F v ⊆ A v` to every variable `v` --
the values the source has not ruled out for `v`. This generalizes the
crisp `frame a : V → Option W` of `Ste.FiniteInstance` (which only ever
names a singleton or is silent, `Ste.FrameRectangular.frameConstraintSide`)
to an arbitrary subset per variable, and is the semantic primitive
underneath `Ste.HyperFrame`'s concept lattice: every partial feasibility
set is built from possibility-set data of exactly this shape
(`partialFeasibilitySet_eq_lowerPolar`). -/
def SetValuedFrame (V : Type*) (A : V → Type*) : Type _ :=
  ∀ v, Set (A v)

variable {V : Type*} {A : V → Type*}

/-- The property set (Combettes 1993, §II-C) induced by a set-valued
frame: the box/rectangle of assignments respecting every variable's
possibility set. -/
def propertySet (F : SetValuedFrame V A) : Set (∀ v, A v) :=
  Set.univ.pi F

theorem mem_propertySet {F : SetValuedFrame V A} {f : ∀ v, A v} :
    f ∈ propertySet F ↔ ∀ v, f v ∈ F v :=
  Set.mem_univ_pi

/-- **A set-valued frame's property set is a rectangle.** By
construction it *is* the product `univ.pi F`, so no separate argument is
needed beyond exhibiting the side family. -/
theorem propertySet_isRectangle (F : SetValuedFrame V A) :
    IsRectangle (propertySet F) :=
  ⟨F, rfl⟩

/-- **A set-valued frame's constraint has vanishing Čech obstruction over
every cover.** Immediate from `propertySet_isRectangle` and the general
rectangular-gluing theorem `cechVanishesCover_of_rectangular`
(`Ste.CechCover`): a single source's possibility-set constraint never
couples two variables. -/
theorem propertySet_cechVanishesCover {J : Type*} (F : SetValuedFrame V A)
    (U : J → Set V) (hcover : ∀ v, ∃ j, v ∈ U j) :
    CechVanishesCover (propertySet F) U :=
  cechVanishesCover_of_rectangular (propertySet_isRectangle F) U hcover

/-! ### Corpora of set-valued frames -/

/-- A **corpus** of set-valued frames: one possibility-set frame per
source `i : I` -- the set-valued generalization of `Ste.FiniteInstance`'s
`frame : A → V → Option W` (one author per index `A`, renamed `Src` in
`ofCrisp` below to avoid clashing with the value-family `A` here). -/
abbrev SetValuedCorpus (I V : Type*) (A : V → Type*) : Type _ :=
  I → SetValuedFrame V A

variable {I : Type*}

/-- The feasibility set of a corpus of set-valued frames: the
intersection of every source's property set (Combettes 1993, §II-C,
Eq. (4), `feasibilitySet` of `Ste.Basic`). -/
def corpusFeasibilitySet (F : SetValuedCorpus I V A) : Set (∀ v, A v) :=
  feasibilitySet (fun i => propertySet (F i))

theorem mem_corpusFeasibilitySet {F : SetValuedCorpus I V A}
    {f : ∀ v, A v} :
    f ∈ corpusFeasibilitySet F ↔ ∀ i v, f v ∈ F i v := by
  rw [corpusFeasibilitySet, mem_feasibilitySet]
  exact forall_congr' fun _ => mem_propertySet

/-- **The corpus feasibility set is itself a rectangle**, with side
`⋂ i, F i v` at variable `v`: intersecting set-valued frames intersects
their possibility sets pointwise. The instance of
`rectangular_feasibilitySet` (`Ste.Sheaf`) for the family
`fun i => propertySet (F i)`. -/
theorem corpusFeasibilitySet_isRectangle (F : SetValuedCorpus I V A) :
    IsRectangle (corpusFeasibilitySet F) :=
  ⟨fun v => ⋂ i, F i v, rectangular_feasibilitySet F⟩

/-- **A corpus of set-valued frames glues over every cover** -- the
headline gluing theorem, generalizing
`Ste.FrameRectangular.frame_cechVanishesCover` from crisp to set-valued
frames. Immediate from `corpusFeasibilitySet_isRectangle` and
`cechVanishesCover_of_rectangular` (`Ste.CechCover`): no new gluing
argument, only the rectangle fact. -/
theorem corpusFeasibilitySet_cechVanishesCover {J : Type*}
    (F : SetValuedCorpus I V A) (U : J → Set V) (hcover : ∀ v, ∃ j, v ∈ U j) :
    CechVanishesCover (corpusFeasibilitySet F) U :=
  cechVanishesCover_of_rectangular (corpusFeasibilitySet_isRectangle F) U hcover

/-! ### Feasibility is a per-variable test -/

/-- **The headline per-variable characterization.** A corpus of
set-valued frames is feasible iff, at EVERY variable, the sources'
possibility sets have a common point -- feasibility is exactly
per-variable possibility-set intersection. This is the set-valued
generalization of
`Ste.FiniteInstance.consistent_iff_forall_disagreementDegree_le_one`
(there: disagreement degree ≤ 1 per variable; here: nonempty
intersection of possibility sets per variable), and follows at once from
`corpusFeasibilitySet_isRectangle` / `rectangular_feasibilitySet`
together with `Set.univ_pi_nonempty_iff`. -/
theorem corpusFeasibilitySet_nonempty_iff (F : SetValuedCorpus I V A) :
    (corpusFeasibilitySet F).Nonempty ↔ ∀ v, (⋂ i, F i v).Nonempty := by
  have h : corpusFeasibilitySet F = Set.univ.pi (fun v => ⋂ i, F i v) :=
    rectangular_feasibilitySet F
  rw [h, Set.univ_pi_nonempty_iff]

/-!
**Remark: pairwise per-variable compatibility does not suffice in
general.** Unlike crisp frame corpora (`Ste.FiniteInstance`), which have
Helly number 2 (`Ste.HellyConsistency.frame_hasHelly_two`), a general
set-valued corpus need not: `corpusFeasibilitySet_nonempty_iff` reduces
global feasibility to a per-variable *intersection* test `⋂ i, F i v`,
and arbitrary possibility sets can fail pairwise-implies-global exactly
as in `Ste.HellyConsistency.exists_not_hasHelly_two` (the classical
3-set counterexample lives at a single variable: three sources whose
possibility sets pairwise overlap there, with empty triple
intersection). Helly-2 for frame corpora is special to possibility sets
that are always a singleton or the whole space
(`Ste.FrameRectangular.frameConstraintSide`); `hasHelly_ofCrisp_two`
below recovers it in exactly that special case.
-/

/-! ### Bridge to `Ste.HyperFrame` -/

/-- **The corpus feasibility set is an extent.** `corpusFeasibilitySet F`
is the extent, at the full constraint set `Set.univ`, of the concept
lattice of the corpus's satisfaction relation
`sat (fun i => propertySet (F i))` -- the closed feasible sets of a
set-valued corpus are exactly the `Ste.HyperFrame` extents built from its
possibility-set data. Via `partialFeasibilitySet_univ` (`Ste.Basic`) and
`isExtent_partialFeasibilitySet` (`Ste.HyperFrame`). -/
theorem isExtent_corpusFeasibilitySet (F : SetValuedCorpus I V A) :
    Order.IsExtent (sat (fun i => propertySet (F i))) (corpusFeasibilitySet F) := by
  rw [corpusFeasibilitySet, ← partialFeasibilitySet_univ]
  exact isExtent_partialFeasibilitySet _ _

/-! ### The crisp case: `frameConstraint` recovered -/

variable {W : Type*} {Src : Type*}

/-- **The crisp set-valued frame** induced by one source's partial
assignment `frame a : V → Option W` (`Ste.FiniteInstance`): the
singleton `{x}` where the source speaks, `univ` (full possibility) where
it is silent. Exactly `Ste.FrameRectangular.frameConstraintSide`, read
in set-valued-frame vocabulary: the crisp frame is the singleton special
case of a `SetValuedFrame`. -/
def ofCrisp (frame : Src → V → Option W) (a : Src) :
    SetValuedFrame V (fun _ => W) :=
  frameConstraintSide frame a

/-- **Agreement.** The property set of the crisp set-valued frame
`ofCrisp frame a` is exactly the original `frameConstraint frame a`
(`Ste.FiniteInstance`) -- reading a crisp frame as a `SetValuedFrame`
recovers the SAME feasibility notion, not merely an analogous one. -/
theorem propertySet_ofCrisp (frame : Src → V → Option W) (a : Src) :
    propertySet (ofCrisp frame a) = frameConstraint frame a :=
  (frameConstraint_eq_pi frame a).symm

/-- **Corpus-level agreement.** Reading a crisp `Ste.FiniteInstance`
frame corpus as a set-valued corpus via `ofCrisp`, source by source,
recovers exactly the same feasibility set. -/
theorem corpusFeasibilitySet_ofCrisp (frame : Src → V → Option W) :
    corpusFeasibilitySet (fun a => ofCrisp frame a)
      = feasibilitySet (frameConstraint frame) := by
  simp only [corpusFeasibilitySet, propertySet_ofCrisp]

/-- **Helly-2 for crisp set-valued corpora.** Transports
`frame_hasHelly_two` (`Ste.HellyConsistency`) along the agreement lemma
`propertySet_ofCrisp`: for the crisp special case of a `SetValuedFrame`
corpus (singleton-or-`univ` sides), pairwise per-variable compatibility
already certifies global feasibility -- unlike the general case (see the
remark after `corpusFeasibilitySet_nonempty_iff`). -/
theorem hasHelly_ofCrisp_two [Fintype Src] [DecidableEq Src] [Fintype V]
    [DecidableEq W] [Inhabited W] (frame : Src → V → Option W) :
    HasHelly (fun a => propertySet (ofCrisp frame a)) 2 := by
  have hS : (fun a => propertySet (ofCrisp frame a)) = frameConstraint frame :=
    funext (propertySet_ofCrisp frame)
  rw [hS]
  exact frame_hasHelly_two frame

end STE
