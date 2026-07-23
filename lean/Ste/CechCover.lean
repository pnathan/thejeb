/-
Čech gluing over ARBITRARY covers of the variable set.

`Ste.CechObstruction` mechanized the gluing obstruction for the
SINGLETON cover `{v}`, where overlaps are empty and compatibility is
vacuous, and `Ste.CouplingLowerBound` closed that case as an iff
(`cechVanishes_iff_rectangular`).  This file lifts the gluing/sheaf
level of that story to an arbitrary cover `U : J → Set V` of the
variable set — any index type `J`, finite or not, with possibly
NONEMPTY overlaps, so the Čech compatibility condition (agreement of
local sections on overlaps) is now substantive.

**Definitions.**  A *compatible family* for the cover
(`CompatibleFamily`) assigns to each context `U j` a genuine local
section of the constraint `T` (a member of `localSections T (U j)`,
`Ste.VariablePresheaf`) such that any two assigned sections agree on
the overlap of their contexts.  The family *glues* (`GluesCover`) when
it is the family of restrictions of a single global section of `T`.
The obstruction *vanishes for the cover* (`CechVanishesCover`) when
every compatible family glues.

**Results (all machine-checked, no `sorry`).**

* *The headline — a genuine sheaf theorem for rectangles over
  arbitrary covers* (`rectangular_cechVanishesCover`): for a
  rectangular constraint `univ.pi P` and ANY cover of `V`, every
  compatible family of local sections glues to a global section.  The
  glue picks, for each variable `v`, a covering context via
  `Classical` choice and reads off the section's value there;
  overlap agreement makes the choice immaterial and makes the glue
  restrict correctly, and rectangularity puts it in the constraint.
  With `glueCover_unique` (glues along a cover are unique) this is
  existence-and-uniqueness (`rectangular_glueCover_existsUnique`) —
  the variable-side presheaf of a rectangle is a sheaf for every
  cover, generalizing the singleton-cover `rectangular_cechVanishes`.

* *Corollary* (`cechVanishesCover_of_rectangular`): any constraint
  admitting a rectangular representation has vanishing obstruction for
  every cover.

* *Bridge to the singleton cover*
  (`cechVanishesCover_singleton_iff`): for the cover `fun v => {v}`
  the general definition coincides with the `CechVanishes` of
  `Ste.CechObstruction`, so the closed singleton-cover theory is the
  instance `U = singletons` of this file.  In particular the coupling
  constraint `diagonal` witnesses genuine FAILURE of the cover-level
  sheaf condition (`diagonal_not_cechVanishesCover`), so vanishing
  for all covers is not automatic.

* *Cover-dependence* (`cechVanishesCover_univ`): for the trivial
  one-context cover `U = univ` every constraint glues — the
  obstruction genuinely depends on the cover, with singletons the
  finest (hardest) case.

* *The `Ȟ⁰`-level obstruction number* (`coverCechObstruction`): the
  extended-natural count `|compatible| - |glued|` for the cover, zero
  whenever vanishing holds (`coverCechObstruction_eq_zero`), hence
  zero for rectangles over every cover
  (`rectangular_coverCechObstruction`).

**Honest boundary.**  This file lifts the GLUING/SHEAF level (`Ȟ⁰`
exactness: compatible families = glued families) from the singleton
cover to arbitrary covers.  The full Čech `Ȟ¹` as a linearized cochain
complex — `C⁰ → C¹` with a coboundary map over a free module,
cohomology as `ker/im`, relative cohomology with local coefficients —
and the quantitative claim "obstruction size = forced representation
blow-up" for general constraint families remain the cited
Abramsky–Brandenburger framework and OUTLOOK; they are not claimed,
and not mechanized, here.

Reference: S. Abramsky, A. Brandenburger, *The sheaf-theoretic
structure of non-locality and contextuality*, New J. Phys. 13 (2011)
113036 (`abramsky2011sheaf`).
-/
import Ste.VariablePresheaf
import Ste.CechObstruction

namespace STE

open Set

variable {V : Type*} {A : V → Type*} {J : Type*}

/-! ### Compatible families and gluing for an arbitrary cover -/

/-- **Compatible family of local sections for a cover** `U : J → Set V`
of the variable set: each context `U j` carries a genuine local section
of the constraint `T` (an extendable partial assignment,
`localSections`), and any two sections agree on the overlap of their
contexts.  For covers with nonempty overlaps the second condition is
substantive — this is the Čech compatibility (cocycle) condition. -/
def CompatibleFamily (T : Set (∀ v, A v)) (U : J → Set V)
    (s : ∀ j, ∀ v : (U j), A v) : Prop :=
  (∀ j, s j ∈ localSections T (U j)) ∧
    ∀ j k (v : V) (hv : v ∈ U j) (hv' : v ∈ U k), s j ⟨v, hv⟩ = s k ⟨v, hv'⟩

/-- A family of local sections over the cover **glues** when it is the
family of restrictions of a single global section of `T`. -/
def GluesCover (T : Set (∀ v, A v)) (U : J → Set V)
    (s : ∀ j, ∀ v : (U j), A v) : Prop :=
  ∃ f ∈ T, ∀ j, (U j).restrict f = s j

/-- **The Čech obstruction of the cover vanishes**: every compatible
family of local sections glues to a global section.  This is the sheaf
condition for the cover `U`. -/
def CechVanishesCover (T : Set (∀ v, A v)) (U : J → Set V) : Prop :=
  ∀ s, CompatibleFamily T U s → GluesCover T U s

/-- Every global section of `T` induces a compatible family over any
cover: restrict it to each context.  Overlap agreement is automatic. -/
theorem compatibleFamily_restrict {T : Set (∀ v, A v)} (U : J → Set V)
    {f : ∀ v, A v} (hf : f ∈ T) :
    CompatibleFamily T U (fun j => (U j).restrict f) :=
  ⟨fun j => restrict_mem_localSections _ hf, fun _ _ _ _ _ => rfl⟩

/-- The induced family of a global section glues (to that section). -/
theorem gluesCover_restrict {T : Set (∀ v, A v)} (U : J → Set V)
    {f : ∀ v, A v} (hf : f ∈ T) :
    GluesCover T U (fun j => (U j).restrict f) :=
  ⟨f, hf, fun _ => rfl⟩

/-- **Glues along a cover are unique**: two global assignments
restricting to the same family of local sections over a cover of `V`
are equal — every variable lies in some context, where both are pinned
by the section there.  (Membership in `T` is not needed.) -/
theorem glueCover_unique {U : J → Set V} (hcover : ∀ v, ∃ j, v ∈ U j)
    {s : ∀ j, ∀ v : (U j), A v} {f f' : ∀ v, A v}
    (hf : ∀ j, (U j).restrict f = s j) (hf' : ∀ j, (U j).restrict f' = s j) :
    f = f' := by
  funext v
  obtain ⟨j, hj⟩ := hcover v
  have h1 : f v = s j ⟨v, hj⟩ := congrFun (hf j) ⟨v, hj⟩
  have h2 : f' v = s j ⟨v, hj⟩ := congrFun (hf' j) ⟨v, hj⟩
  rw [h1, h2]

/-! ### The headline: rectangles glue over every cover -/

/-- **The sheaf theorem for rectangular constraints over an arbitrary
cover.**  For a product constraint `univ.pi P` and ANY cover
`U : J → Set V` of the variable set, every compatible family of local
sections glues to a global section.  The glue: for each variable `v`
pick (by choice, from `hcover`) a context containing it and read off
the local section's value there — well-defined in effect because
overlap agreement makes any two choices agree, in the constraint
because each local section of the product lands coordinatewise in `P`,
and restricting to the prescribed sections again by overlap agreement.
This generalizes `rectangular_cechVanishes` (singleton cover,
`Ste.CechObstruction`) to covers with substantive overlaps. -/
theorem rectangular_cechVanishesCover (P : ∀ v, Set (A v))
    (U : J → Set V) (hcover : ∀ v, ∃ j, v ∈ U j) :
    CechVanishesCover (Set.univ.pi P) U := by
  rintro s ⟨hsec, hcompat⟩
  refine ⟨fun v => s (hcover v).choose ⟨v, (hcover v).choose_spec⟩,
    Set.mem_univ_pi.mpr fun v => ?_, fun j => ?_⟩
  · -- each coordinate of the glue lies in `P v`, because the chosen
    -- context's section extends to a global section of the product
    show s (hcover v).choose ⟨v, (hcover v).choose_spec⟩ ∈ P v
    obtain ⟨g, hg, hgs⟩ := hsec (hcover v).choose
    have hgv : g v = s (hcover v).choose ⟨v, (hcover v).choose_spec⟩ :=
      congrFun hgs ⟨v, (hcover v).choose_spec⟩
    exact hgv ▸ Set.mem_univ_pi.mp hg v
  · -- the glue restricts to the prescribed section on each context,
    -- by agreement on the overlap of `U j` with the chosen context
    funext u
    obtain ⟨u, hu⟩ := u
    exact hcompat (hcover u).choose j u (hcover u).choose_spec hu

/-- **Existence and uniqueness of the glue for rectangles**: over any
cover, a compatible family of local sections of a product constraint
glues to a *unique* global section — the full sheaf
existence-and-uniqueness condition. -/
theorem rectangular_glueCover_existsUnique (P : ∀ v, Set (A v))
    (U : J → Set V) (hcover : ∀ v, ∃ j, v ∈ U j)
    {s : ∀ j, ∀ v : (U j), A v}
    (hs : CompatibleFamily (Set.univ.pi P) U s) :
    ∃! f : ∀ v, A v, f ∈ Set.univ.pi P ∧ ∀ j, (U j).restrict f = s j := by
  obtain ⟨f, hf, hres⟩ := rectangular_cechVanishesCover P U hcover s hs
  exact ⟨f, ⟨hf, hres⟩, fun g hg => glueCover_unique hcover hg.2 hres⟩

/-- **Vanishing for every cover, representation form**: any constraint
admitting a rectangular representation has vanishing Čech obstruction
for every cover of the variable set. -/
theorem cechVanishesCover_of_rectangular {T : Set (∀ v, A v)}
    (hT : ∃ P : ∀ v, Set (A v), T = Set.univ.pi P)
    (U : J → Set V) (hcover : ∀ v, ∃ j, v ∈ U j) :
    CechVanishesCover T U := by
  obtain ⟨P, rfl⟩ := hT
  exact rectangular_cechVanishesCover P U hcover

/-! ### The trivial cover: obstruction depends on the cover -/

/-- For the one-context cover by `univ`, EVERY constraint has vanishing
obstruction: a compatible family is a single local section, i.e. the
restriction of some global section, which glues it.  Vanishing is
genuinely cover-dependent — the singleton cover below is the finest
and hardest case. -/
theorem cechVanishesCover_univ (T : Set (∀ v, A v)) :
    CechVanishesCover T (fun _ : PUnit => (Set.univ : Set V)) := by
  rintro s ⟨hsec, -⟩
  obtain ⟨f, hf, hfs⟩ := hsec PUnit.unit
  exact ⟨f, hf, fun j => by cases j; exact hfs⟩

/-! ### The singleton-cover instance recovers `CechVanishes` -/

/-- Cover-level vanishing at the singleton cover implies the
singleton-cover vanishing of `Ste.CechObstruction`: a compatible family
in the old sense (a point of the projection rectangle) induces a
compatible family of the cover `fun v => {v}`, whose glue is the
required global section. -/
theorem cechVanishes_of_cechVanishesCover_singleton {T : Set (∀ v, A v)}
    (h : CechVanishesCover T (fun v : V => ({v} : Set V))) :
    CechVanishes T := by
  intro t ht
  have hcomp : CompatibleFamily T (fun v : V => ({v} : Set V))
      (fun j => ({j} : Set V).restrict t) := by
    refine ⟨fun j => ?_, fun _ _ _ _ _ => rfl⟩
    obtain ⟨g, hg, hgj⟩ := Set.mem_univ_pi.mp ht j
    exact ⟨g, hg, restrict_singleton_eq_iff.mpr hgj⟩
  obtain ⟨f, hf, hres⟩ := h _ hcomp
  have hft : f = t := funext fun v => congrFun (hres v) ⟨v, rfl⟩
  exact ⟨ht, glues_iff_mem.mpr (hft ▸ hf)⟩

/-- Singleton-cover vanishing of `Ste.CechObstruction` implies
cover-level vanishing at the singleton cover: read a compatible family
of the cover as a point of the projection rectangle (its value at each
`{v}`), glue by the old vanishing, and check the restrictions. -/
theorem cechVanishesCover_singleton_of_cechVanishes {T : Set (∀ v, A v)}
    (h : CechVanishes T) :
    CechVanishesCover T (fun v : V => ({v} : Set V)) := by
  rintro s ⟨hsec, -⟩
  have ht : (fun v => s v ⟨v, rfl⟩) ∈ compatibleFamilies T := by
    refine Set.mem_univ_pi.mpr fun v => ?_
    obtain ⟨g, hg, hgs⟩ := hsec v
    exact ⟨g, hg, congrFun hgs ⟨v, rfl⟩⟩
  obtain ⟨-, hglue⟩ := h ht
  refine ⟨fun v => s v ⟨v, rfl⟩, glues_iff_mem.mp hglue, fun j => ?_⟩
  funext u
  obtain ⟨u, hu⟩ := u
  have hu' : u = j := Set.mem_singleton_iff.mp hu
  subst hu'
  rfl

/-- **The singleton-cover bridge**: for the cover of `V` by singletons,
the cover-level sheaf condition of this file coincides with the
`CechVanishes` of `Ste.CechObstruction`.  The closed singleton-cover
theory (`cechVanishes_iff_rectangular`, `Ste.CouplingLowerBound`) is
the instance `U = fun v => {v}` of the general definition. -/
theorem cechVanishesCover_singleton_iff (T : Set (∀ v, A v)) :
    CechVanishesCover T (fun v : V => ({v} : Set V)) ↔ CechVanishes T :=
  ⟨cechVanishes_of_cechVanishesCover_singleton,
    cechVanishesCover_singleton_of_cechVanishes⟩

/-- **Cover-level gluing genuinely fails at the coupling**: the
diagonal constraint does not satisfy the sheaf condition for its
singleton cover, via the bridge and `diagonal_not_cechVanishes`.  So
vanishing over all covers is not automatic, and the rectangular sheaf
theorem above has real content. -/
theorem diagonal_not_cechVanishesCover :
    ¬CechVanishesCover diagonal
      (fun v : Fin 2 => ({v} : Set (Fin 2))) := fun h =>
  diagonal_not_cechVanishes (cechVanishes_of_cechVanishesCover_singleton h)

/-! ### The `Ȟ⁰`-level obstruction for a cover -/

/-- The set of compatible families of local sections for the cover. -/
def coverCompatibleFamilies (T : Set (∀ v, A v)) (U : J → Set V) :
    Set (∀ j, ∀ v : (U j), A v) :=
  {s | CompatibleFamily T U s}

/-- The compatible families that actually glue to a global section. -/
def coverGluedFamilies (T : Set (∀ v, A v)) (U : J → Set V) :
    Set (∀ j, ∀ v : (U j), A v) :=
  {s | CompatibleFamily T U s ∧ GluesCover T U s}

/-- Glued families are compatible. -/
theorem coverGluedFamilies_subset (T : Set (∀ v, A v)) (U : J → Set V) :
    coverGluedFamilies T U ⊆ coverCompatibleFamilies T U :=
  fun _ hs => hs.1

/-- Vanishing for the cover is exactly: every compatible family is a
glued family. -/
theorem cechVanishesCover_iff_subset (T : Set (∀ v, A v)) (U : J → Set V) :
    CechVanishesCover T U ↔
      coverCompatibleFamilies T U ⊆ coverGluedFamilies T U :=
  ⟨fun h s hs => ⟨hs, h s hs⟩, fun h s hs => (h hs).2⟩

/-- **The Čech obstruction number of a cover**: how many compatible
families of local sections fail to glue, as a difference of
extended-natural counts — the cover-level generalization of
`cechObstruction` (`Ste.CechObstruction`).  Zero means the sheaf
condition holds for this cover (in the finite case). -/
noncomputable def coverCechObstruction (T : Set (∀ v, A v))
    (U : J → Set V) : ℕ∞ :=
  (coverCompatibleFamilies T U).encard - (coverGluedFamilies T U).encard

/-- Vanishing makes the obstruction number zero: the compatible and
glued families coincide. -/
theorem coverCechObstruction_eq_zero {T : Set (∀ v, A v)}
    {U : J → Set V} (h : CechVanishesCover T U) :
    coverCechObstruction T U = 0 := by
  unfold coverCechObstruction
  rw [Set.Subset.antisymm (coverGluedFamilies_subset T U)
    ((cechVanishesCover_iff_subset T U).mp h)]
  exact tsub_self _

/-- **`Ȟ⁰`-exactness for rectangles over every cover, numerically**:
the obstruction number of a rectangular constraint vanishes for any
cover of the variable set. -/
theorem rectangular_coverCechObstruction (P : ∀ v, Set (A v))
    (U : J → Set V) (hcover : ∀ v, ∃ j, v ∈ U j) :
    coverCechObstruction (Set.univ.pi P) U = 0 :=
  coverCechObstruction_eq_zero (rectangular_cechVanishesCover P U hcover)

end STE
