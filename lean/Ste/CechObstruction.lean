/-
The concrete Čech obstruction for the singleton cover of a product
hypothesis space, computed sorry-free on the two-variable Boolean
instance.

Following Abramsky–Brandenburger (*The sheaf-theoretic structure of
non-locality and contextuality*, 2011, `abramsky2011sheaf`), the failure
to glue compatible local sections into a global one is measured by a
Čech cohomology class of the cover of contexts; it vanishes exactly when
gluing succeeds.  This file mechanizes the SMALLEST honest instance of
that picture in the STE setting — it does NOT build the general Čech
`Ȟ¹` functor.

**The instance.**  Variables `V` with value types `A v`, constraint
`T ⊆ ∀ v, A v`; the cover of `V` is by the singleton contexts `{v}`
(`singletonCover_cover`).  The local sections of `T` over `{v}` are the
values at `v` attained by some global section — the projection
`contextSections T v`.  Distinct singleton contexts have EMPTY overlap
(`singletonCover_overlap_empty`), so the Čech compatibility condition
(agreement on overlaps) is vacuous: a *compatible family* is exactly one
local section per context, i.e. a point of the rectangle
`univ.pi (contextSections T)` (`compatibleFamilies`).  A family *glues*
(`Glues`) when it is the restriction of a global section of `T`; over
the singleton cover this holds iff the family, read as an assignment,
lies in `T` (`glues_iff_mem`, `gluedFamilies_eq`).

**The invariant.**  `cechObstruction T` is the (extended-natural) count
`|compatible families| - |glued families|`.  This is the concrete `Ȟ¹`
obstruction number for this cover: it is `0` iff no compatible family is
stuck (in the finite case), and each stuck family is a nontrivial
cocycle in the Abramsky–Brandenburger sense.

**Results (all machine-checked, no `sorry`).**

* *Nonvanishing on the coupling constraint.*  For the `diagonal`
  (`f 0 = f 1` on two Booleans, `Ste.Sheaf`): both projections are full
  (`contextSections_diagonal`), so there are `2 × 2 = 4` compatible
  families (`compatibleFamilies_diagonal_encard`) but only `2` glue
  (`gluedFamilies_diagonal_encard`, reusing `diagonal_encard`):
  `cechObstruction diagonal = 2 ≠ 0` (`diagonal_cechObstruction`,
  `diagonal_cechObstruction_ne_zero`).  The mixed family
  `x ↦ false, y ↦ true` is an explicit compatible-but-stuck cocycle
  (`diagonal_mixed_compatible_not_glues`).

* *Vanishing on rectangular constraints.*  For any product constraint
  `univ.pi P`, every compatible family glues
  (`rectangular_cechVanishes`, `compatibleFamilies_pi`), so
  `cechObstruction (univ.pi P) = 0` (`rectangular_cechObstruction`) —
  the `Ȟ¹ = 0` case.

* *Bridge to the representation obstruction.*  Vanishing forces the
  constraint to BE a rectangle (`rectangular_of_cechVanishes`), so
  `diagonal_not_rectangular` (`Ste.Sheaf`) yields nonvanishing a second
  way (`diagonal_not_cechVanishes`): the Čech obstruction of this cover
  and the rectangular-representation obstruction are the same
  phenomenon.

**Honest boundary.**  What is proven here is exactly the obstruction for
the SINGLETON cover on a product space, with the two-variable Boolean
diagonal as the computed nonvanishing witness.  The general cohomological
theory — arbitrary covers with nonempty overlaps, genuine cochain
complexes and the full `Ȟ¹` functor, relative cohomology with local
coefficients, and the quantitative claim "obstruction size = forced
representation blow-up" for general constraint families — is the cited
Abramsky–Brandenburger framework and OUTLOOK; it is not claimed, and not
mechanized, in this file.

Reference: S. Abramsky, A. Brandenburger, *The sheaf-theoretic structure
of non-locality and contextuality*, New J. Phys. 13 (2011) 113036
(`abramsky2011sheaf`).
-/
import Mathlib.Data.Set.Card
import Mathlib.Data.ENat.Basic
import Mathlib.Tactic.NormNum
import Ste.Sheaf

namespace STE

open Set

variable {V : Type*} {A : V → Type*}

/-! ### The singleton cover and its (empty) overlaps -/

/-- The singleton contexts `{v}` cover the variable set: this is the
cover whose Čech obstruction we compute. -/
theorem singletonCover_cover : ⋃ v : V, ({v} : Set V) = Set.univ :=
  Set.iUnion_of_singleton V

/-- Distinct singleton contexts have empty overlap.  Hence the Čech
compatibility condition — agreement of local sections on overlaps — is
vacuous for this cover, and `compatibleFamilies` below is honestly the
set of ALL compatible families. -/
theorem singletonCover_overlap_empty {v w : V} (h : v ≠ w) :
    ({v} : Set V) ∩ {w} = ∅ := by
  ext u
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, iff_false, not_and]
  rintro rfl
  exact h

/-! ### Local sections, compatible families, gluing -/

/-- The local sections of the constraint `T` over the singleton context
`{v}`: the values at `v` attained by some global section of `T` — the
projection of `T` to coordinate `v`. -/
def contextSections (T : Set (∀ v, A v)) (v : V) : Set (A v) :=
  (fun f => f v) '' T

/-- The compatible families of local sections for the singleton cover:
one local section per context, agreement on (empty) overlaps being
vacuous.  This is the rectangle spanned by the projections of `T`. -/
def compatibleFamilies (T : Set (∀ v, A v)) : Set (∀ v, A v) :=
  Set.univ.pi (contextSections T)

/-- A family of local sections *glues* when it is the restriction of a
single global section of the constraint `T`. -/
def Glues (T : Set (∀ v, A v)) (s : ∀ v, A v) : Prop :=
  ∃ g ∈ T, ∀ v, g v = s v

/-- Over the singleton cover, a family glues iff, read as a global
assignment, it lies in the constraint. -/
theorem glues_iff_mem {T : Set (∀ v, A v)} {s : ∀ v, A v} :
    Glues T s ↔ s ∈ T := by
  constructor
  · rintro ⟨g, hg, hgs⟩
    rwa [show g = s from funext hgs] at hg
  · exact fun hs => ⟨s, hs, fun _ => rfl⟩

/-- Every global section restricts to a compatible family: restriction
lands in `compatibleFamilies`. -/
theorem subset_compatibleFamilies (T : Set (∀ v, A v)) :
    T ⊆ compatibleFamilies T := fun f hf =>
  Set.mem_univ_pi.mpr fun v => ⟨f, hf, rfl⟩

/-- The compatible families that actually glue to a global section. -/
def gluedFamilies (T : Set (∀ v, A v)) : Set (∀ v, A v) :=
  {s ∈ compatibleFamilies T | Glues T s}

/-- The glued families are exactly the global sections of `T`. -/
theorem gluedFamilies_eq (T : Set (∀ v, A v)) : gluedFamilies T = T := by
  ext s
  constructor
  · rintro ⟨-, hg⟩
    exact glues_iff_mem.mp hg
  · exact fun hs => ⟨subset_compatibleFamilies T hs, glues_iff_mem.mpr hs⟩

/-! ### The obstruction invariant -/

/-- **The concrete Čech obstruction number** of the constraint `T` for
the singleton cover: how many compatible families of local sections fail
to glue to a global section, as the difference of extended-natural
counts.  In the Abramsky–Brandenburger picture this is the size of the
nontrivial part of `Ȟ¹` for this cover; `0` means every compatible
family glues (the sheaf condition holds). -/
noncomputable def cechObstruction (T : Set (∀ v, A v)) : ℕ∞ :=
  (compatibleFamilies T).encard - (gluedFamilies T).encard

/-- The obstruction *vanishes* when every compatible family glues. -/
def CechVanishes (T : Set (∀ v, A v)) : Prop :=
  compatibleFamilies T ⊆ gluedFamilies T

/-- Vanishing is exactly: the constraint already equals the rectangle of
its compatible families. -/
theorem cechVanishes_iff (T : Set (∀ v, A v)) :
    CechVanishes T ↔ compatibleFamilies T = T := by
  unfold CechVanishes
  rw [gluedFamilies_eq]
  exact ⟨fun h => Set.Subset.antisymm h (subset_compatibleFamilies T),
    fun h => le_of_eq h⟩

/-- **Vanishing forces rectangularity**: if every compatible family
glues, the constraint is a product (rectangle) — its own projection
rectangle.  This bridges the Čech obstruction of the singleton cover to
the representation obstruction of `Ste.Sheaf`. -/
theorem rectangular_of_cechVanishes {T : Set (∀ v, A v)}
    (h : CechVanishes T) : ∃ t : ∀ v, Set (A v), T = Set.univ.pi t :=
  ⟨contextSections T, ((cechVanishes_iff T).mp h).symm⟩

/-! ### Vanishing for rectangular constraints (the `Ȟ¹ = 0` case) -/

/-- Projections of a rectangle are contained in its sides. -/
theorem contextSections_pi_subset (P : ∀ v, Set (A v)) (v : V) :
    contextSections (Set.univ.pi P) v ⊆ P v := by
  rintro b ⟨f, hf, rfl⟩
  exact Set.mem_univ_pi.mp hf v

/-- For a rectangular constraint the compatible families are exactly the
constraint itself: nothing new appears when the sections are recombined. -/
theorem compatibleFamilies_pi (P : ∀ v, Set (A v)) :
    compatibleFamilies (Set.univ.pi P) = Set.univ.pi P := by
  refine Set.Subset.antisymm ?_ (subset_compatibleFamilies _)
  intro f hf
  have hf' : ∀ v, f v ∈ contextSections (Set.univ.pi P) v :=
    Set.mem_univ_pi.mp hf
  exact Set.mem_univ_pi.mpr fun v => contextSections_pi_subset P v (hf' v)

/-- **Rectangular constraints have vanishing obstruction**: every
compatible family of local sections glues to a global section. -/
theorem rectangular_cechVanishes (P : ∀ v, Set (A v)) :
    CechVanishes (Set.univ.pi P) :=
  (cechVanishes_iff _).mpr (compatibleFamilies_pi P)

/-- For a rectangular constraint the glued count equals the compatible
count — no compatible family is stuck. -/
theorem rectangular_glued_encard_eq_compatible (P : ∀ v, Set (A v)) :
    (gluedFamilies (Set.univ.pi P)).encard
      = (compatibleFamilies (Set.univ.pi P)).encard := by
  rw [gluedFamilies_eq, compatibleFamilies_pi]

/-- **`Ȟ¹ = 0` for rectangles**: the Čech obstruction number of any
rectangular (variable-separable) constraint is zero. -/
theorem rectangular_cechObstruction (P : ∀ v, Set (A v)) :
    cechObstruction (Set.univ.pi P) = 0 := by
  unfold cechObstruction
  rw [gluedFamilies_eq, compatibleFamilies_pi]
  exact tsub_self _

/-! ### Nonvanishing for the coupling constraint (the computed witness) -/

/-- Both projections of the diagonal are full: locally, each variable is
completely unconstrained.  All the information of the coupling lives in
the correlation, none in the margins. -/
theorem contextSections_diagonal (v : Fin 2) :
    contextSections diagonal v = Set.univ :=
  Set.eq_univ_of_forall fun b => ⟨fun _ => b, rfl, rfl⟩

/-- Every family of local sections is compatible for the diagonal: the
compatible families are the whole four-point space. -/
theorem compatibleFamilies_diagonal :
    compatibleFamilies diagonal = Set.univ := by
  refine Set.eq_univ_of_forall fun f => Set.mem_univ_pi.mpr fun v => ?_
  rw [contextSections_diagonal]
  exact Set.mem_univ _

/-- The diagonal admits `2 × 2 = 4` compatible families of local
sections. -/
theorem compatibleFamilies_diagonal_encard :
    (compatibleFamilies diagonal).encard = 4 := by
  rw [compatibleFamilies_diagonal, encard_univ_two_bits]

/-- Only `2` of the compatible families glue — the two constant
assignments (reusing `diagonal_encard`). -/
theorem gluedFamilies_diagonal_encard :
    (gluedFamilies diagonal).encard = 2 := by
  rw [gluedFamilies_eq, diagonal_encard]

/-- The explicit stuck cocycle: the mixed family `x ↦ false, y ↦ true`
is a compatible family of local sections that is the restriction of no
global section of the diagonal. -/
theorem diagonal_mixed_compatible_not_glues :
    (fun v : Fin 2 => decide (v = 1)) ∈ compatibleFamilies diagonal ∧
      ¬Glues diagonal (fun v : Fin 2 => decide (v = 1)) := by
  refine ⟨?_, ?_⟩
  · rw [compatibleFamilies_diagonal]
    exact Set.mem_univ _
  · rw [glues_iff_mem]
    intro hmem
    exact absurd
      (show decide ((0 : Fin 2) = 1) = decide ((1 : Fin 2) = 1) from hmem)
      (by decide)

/-- **The coupling obstruction does not vanish**: some compatible family
of the diagonal fails to glue.  Equivalently (via
`rectangular_of_cechVanishes`) vanishing would make the diagonal
rectangular, contradicting `diagonal_not_rectangular`. -/
theorem diagonal_not_cechVanishes : ¬CechVanishes diagonal := fun h =>
  diagonal_not_rectangular
    ⟨contextSections diagonal, ((cechVanishes_iff diagonal).mp h).symm⟩

/-- The counts disagree: `4` compatible families versus `2` glued ones. -/
theorem diagonal_compatible_encard_ne_glued_encard :
    (compatibleFamilies diagonal).encard
      ≠ (gluedFamilies diagonal).encard := by
  rw [compatibleFamilies_diagonal_encard, gluedFamilies_diagonal_encard]
  first
  | decide
  | norm_num

/-- **The computed obstruction of the diagonal is `2`**: of the `4`
compatible families, exactly the `2` mixed ones are stuck.  This is the
minimal nonvanishing Čech obstruction realized in the STE setting. -/
theorem diagonal_cechObstruction : cechObstruction diagonal = 2 := by
  unfold cechObstruction
  rw [compatibleFamilies_diagonal_encard, gluedFamilies_diagonal_encard]
  first
  | exact rfl
  | decide
  | norm_num [← ENat.coe_sub]

/-- **Nonvanishing, numerically**: the Čech obstruction number of the
coupling constraint is nonzero. -/
theorem diagonal_cechObstruction_ne_zero :
    cechObstruction diagonal ≠ 0 := by
  rw [diagonal_cechObstruction]
  first
  | decide
  | norm_num

end STE
