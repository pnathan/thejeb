/-
The linearized Čech cochain complex, with cohomology `Ȟ¹ = ker/im`.

`Ste.CechCover` mechanized the SET-level gluing story: compatible
families of local sections over an arbitrary cover, the sheaf
condition, and its failure at the coupling.  The Abramsky–Brandenburger
framework grades that obstruction COHOMOLOGICALLY: one linearizes the
section presheaf into modules and reads the failure of gluing off a
Čech cochain complex.  This file builds that linearized complex as
honest `R`-modules and `R`-linear maps — no `sorry`, no axioms.

**The complex.**  Fix a commutative ring `R` and an `R`-module `M`
(constant coefficients), and an index type `ι` for the cover.  The
cochain modules are `C⁰ = ι → M`, `C¹ = ι → ι → M`,
`C² = ι → ι → ι → M`, `C³ = ι → ι → ι → ι → M` (functions on tuples of
cover indices — the full nerve, non-alternating presentation), with the
standard alternating-sum coboundaries
`(d⁰f) i j = f j - f i`,
`(d¹g) i j k = g j k - g i k + g i j`,
`(d²h) i j k l = h j k l - h i k l + h i j l - h i j k`,
each a genuine `R`-linear map (`cechD0`, `cechD1`, `cechD2`).

**Results (all machine-checked).**

* *The cochain-complex identities* (`cechComplex_d_comp_d`,
  `cechComplex_d2_comp_d1`): `d¹ ∘ d⁰ = 0` and `d² ∘ d¹ = 0` as
  compositions of linear maps, hence `im d⁰ ≤ ker d¹` and
  `im d¹ ≤ ker d²` (`cechD0_range_le_ker`, `cechD1_range_le_ker`).

* *Cohomology as modules*: `cechH0 = ker d⁰` (global cocycles),
  `cechH1 = ker d¹ ⧸ im d⁰` and `cechH2 = ker d² ⧸ im d¹` as genuine
  quotient `R`-modules (the coboundaries pulled back into the cocycle
  submodule along its inclusion, legitimate by the complex identity).

* *Cocycle identities* (`cechCocycle_diag`, `cechCocycle_antisymm`):
  a 1-cocycle vanishes on the diagonal and is antisymmetric — the
  linearized reflexivity and symmetry of overlap agreement.

* *The vanishing theorem* (`cechH1_subsingleton`,
  `cechH2_subsingleton`): over any NONEMPTY index type — in particular
  any nonempty finite cover `[Fintype ι]` — this constant-coefficient
  full-nerve complex is exact at `C¹` and `C²`:
  `ker d¹ = im d⁰` (`cechD1_ker_eq_range`, every 1-cocycle is the
  coboundary of the explicit primitive `f i = g i₀ i` for a basepoint
  `i₀`), likewise at `C²`, so `Ȟ¹ = 0` and `Ȟ² = 0`.  The nerve of a
  cover in which all overlaps are treated as full is a simplex, and a
  simplex is acyclic.  `Ȟ⁰` is exactly the constants:
  `cechH0EquivCoeff : cechH0 ≃ₗ[R] M`.  No `[DecidableEq ι]` or
  `[Fintype ι]` is needed anywhere — the statements hold for arbitrary
  `ι`, finite covers included.

* *The STE bridge* (`globalZeroCochain_mem_cechH0`,
  `GluesCover.exists_cechH0`, `CompatibleFamily.exists_cechH0`,
  `globalZeroCochain_glue_unique`, `globalZeroCochain_injective`):
  linearizing global sections into the free module `(∀ v, A v) →₀ R`,
  every global section `f` of a constraint yields the constant Čech
  0-cochain `j ↦ single f 1`, which is a 0-cocycle, i.e. an element of
  the linearized `Ȟ⁰`.  Hence every set-level compatible family that
  glues (`Ste.CechCover`) — in particular EVERY compatible family when
  the cover-level obstruction vanishes — is seen by the linearized
  `Ȟ⁰`; over a genuine cover its cocycle is unique (via
  `glueCover_unique`), and distinct global sections give distinct
  cocycles (`single` is injective for `1 ≠ 0`).

**Honest boundary.**  The vanishing `Ȟ¹ = 0` here is for CONSTANT
coefficients on the FULL nerve — the acyclic simplex.  The
contextuality of Abramsky–Brandenburger lives in the RELATIVE
cohomology of the support presheaf with LOCAL coefficients over the
actual (partial) nerve of the measurement cover; building that
presheaf-coefficient complex over the set-level `localSections`, and
the quantitative claim "obstruction size = forced representation
blow-up" (e.g. an inequality between a cohomological rank and the
rectangular-cover number of a coupling), remain OUTLOOK — they are not
claimed, and not mechanized, here.

Reference: S. Abramsky, A. Brandenburger, *The sheaf-theoretic
structure of non-locality and contextuality*, New J. Phys. 13 (2011)
113036 (`abramsky2011sheaf`).
-/
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Tactic.Abel
import Ste.CechCover

namespace STE

section CechComplex

variable (R : Type*) [CommRing R] (ι : Type*) (M : Type*)
  [AddCommGroup M] [Module R M]

/-! ### The cochain modules -/

/-- Degree-0 Čech cochains with constant coefficients `M`: one value
per cover index. -/
abbrev cechC0 := ι → M

/-- Degree-1 Čech cochains: one value per ordered pair of cover
indices (the full nerve, non-alternating presentation). -/
abbrev cechC1 := ι → ι → M

/-- Degree-2 Čech cochains: one value per ordered triple. -/
abbrev cechC2 := ι → ι → ι → M

/-- Degree-3 Čech cochains: one value per ordered quadruple. -/
abbrev cechC3 := ι → ι → ι → ι → M

/-! ### The coboundary maps -/

/-- **The degree-0 Čech coboundary** `(d⁰f) i j = f j - f i`, as an
`R`-linear map: the discrepancy of the local values of `f` across the
overlap `i ∩ j`.  A 0-cochain is a cocycle iff all discrepancies
vanish. -/
def cechD0 : cechC0 ι M →ₗ[R] cechC1 ι M where
  toFun f := fun i j => f j - f i
  map_add' f g := by
    funext i j
    simp only [Pi.add_apply]
    abel
  map_smul' r f := by
    funext i j
    simp only [Pi.smul_apply, RingHom.id_apply, smul_sub]

@[simp] theorem cechD0_apply (f : cechC0 ι M) (i j : ι) :
    cechD0 R ι M f i j = f j - f i := rfl

/-- **The degree-1 Čech coboundary**
`(d¹g) i j k = g j k - g i k + g i j`: the alternating sum of `g` over
the faces of the triangle `(i, j, k)`. -/
def cechD1 : cechC1 ι M →ₗ[R] cechC2 ι M where
  toFun g := fun i j k => g j k - g i k + g i j
  map_add' g₁ g₂ := by
    funext i j k
    simp only [Pi.add_apply]
    abel
  map_smul' r g := by
    funext i j k
    simp only [Pi.smul_apply, RingHom.id_apply, smul_sub, smul_add]

@[simp] theorem cechD1_apply (g : cechC1 ι M) (i j k : ι) :
    cechD1 R ι M g i j k = g j k - g i k + g i j := rfl

/-- **The degree-2 Čech coboundary**
`(d²h) i j k l = h j k l - h i k l + h i j l - h i j k`: the
alternating sum over the faces of the tetrahedron. -/
def cechD2 : cechC2 ι M →ₗ[R] cechC3 ι M where
  toFun h := fun i j k l => h j k l - h i k l + h i j l - h i j k
  map_add' h₁ h₂ := by
    funext i j k l
    simp only [Pi.add_apply]
    abel
  map_smul' r h := by
    funext i j k l
    simp only [Pi.smul_apply, RingHom.id_apply, smul_sub, smul_add]

@[simp] theorem cechD2_apply (h : cechC2 ι M) (i j k l : ι) :
    cechD2 R ι M h i j k l = h j k l - h i k l + h i j l - h i j k := rfl

/-! ### The cochain-complex identities `d ∘ d = 0` -/

/-- **The defining cochain-complex identity**: `d¹ ∘ d⁰ = 0` as a
composition of linear maps.  The coboundary of a coboundary telescopes
to zero. -/
theorem cechComplex_d_comp_d : (cechD1 R ι M).comp (cechD0 R ι M) = 0 := by
  refine LinearMap.ext fun f => ?_
  funext i j k
  simp only [LinearMap.comp_apply, cechD1_apply, cechD0_apply,
    LinearMap.zero_apply, Pi.zero_apply]
  abel

/-- The complex continues one degree up: `d² ∘ d¹ = 0`. -/
theorem cechComplex_d2_comp_d1 :
    (cechD2 R ι M).comp (cechD1 R ι M) = 0 := by
  refine LinearMap.ext fun g => ?_
  funext i j k l
  simp only [LinearMap.comp_apply, cechD2_apply, cechD1_apply,
    LinearMap.zero_apply, Pi.zero_apply]
  abel

/-- 1-coboundaries are 1-cocycles: `im d⁰ ≤ ker d¹`. -/
theorem cechD0_range_le_ker :
    LinearMap.range (cechD0 R ι M) ≤ LinearMap.ker (cechD1 R ι M) :=
  LinearMap.range_le_ker_iff.mpr (cechComplex_d_comp_d R ι M)

/-- 2-coboundaries are 2-cocycles: `im d¹ ≤ ker d²`. -/
theorem cechD1_range_le_ker :
    LinearMap.range (cechD1 R ι M) ≤ LinearMap.ker (cechD2 R ι M) :=
  LinearMap.range_le_ker_iff.mpr (cechComplex_d2_comp_d1 R ι M)

/-! ### Cohomology as `R`-modules -/

/-- **Čech `Ȟ⁰`**: the module of 0-cocycles `ker d⁰` — 0-cochains all
of whose overlap discrepancies vanish, the linearized global
sections. -/
abbrev cechH0 : Submodule R (cechC0 ι M) := LinearMap.ker (cechD0 R ι M)

/-- The 1-coboundaries `im d⁰`, pulled back into the module of
1-cocycles along the inclusion `ker d¹ ↪ C¹` (legitimate since
`im d⁰ ≤ ker d¹` by the complex identity). -/
def cechCoboundaries1 : Submodule R (LinearMap.ker (cechD1 R ι M)) :=
  (LinearMap.range (cechD0 R ι M)).comap
    (LinearMap.ker (cechD1 R ι M)).subtype

/-- **Čech `Ȟ¹ = ker d¹ / im d⁰`**, an honest quotient `R`-module: the
1-cocycles modulo the 1-coboundaries.  This is the linearized
first-cohomology obstruction group of the Abramsky–Brandenburger
framework (`abramsky2011sheaf`). -/
abbrev cechH1 :=
  LinearMap.ker (cechD1 R ι M) ⧸ cechCoboundaries1 R ι M

/-- The 2-coboundaries `im d¹` inside the 2-cocycles. -/
def cechCoboundaries2 : Submodule R (LinearMap.ker (cechD2 R ι M)) :=
  (LinearMap.range (cechD1 R ι M)).comap
    (LinearMap.ker (cechD2 R ι M)).subtype

/-- **Čech `Ȟ² = ker d² / im d¹`** as a quotient `R`-module. -/
abbrev cechH2 :=
  LinearMap.ker (cechD2 R ι M) ⧸ cechCoboundaries2 R ι M

/-! ### Cocycle identities -/

/-- The 1-cocycle relation, pointwise: `g j k - g i k + g i j = 0`. -/
theorem cechCocycle_rel {g : cechC1 ι M}
    (hg : g ∈ LinearMap.ker (cechD1 R ι M)) (i j k : ι) :
    g j k - g i k + g i j = 0 := by
  simpa using congrFun (congrFun (congrFun (LinearMap.mem_ker.mp hg) i) j) k

/-- A 1-cocycle vanishes on the diagonal: no self-discrepancy — the
linearized reflexivity of overlap agreement. -/
theorem cechCocycle_diag {g : cechC1 ι M}
    (hg : g ∈ LinearMap.ker (cechD1 R ι M)) (i : ι) : g i i = 0 := by
  simpa using cechCocycle_rel R ι M hg i i i

/-- A 1-cocycle is antisymmetric: `g j i = -g i j` — the linearized
symmetry of overlap agreement. -/
theorem cechCocycle_antisymm {g : cechC1 ι M}
    (hg : g ∈ LinearMap.ker (cechD1 R ι M)) (i j : ι) :
    g j i = -g i j := by
  have h := cechCocycle_rel R ι M hg i j i
  rw [cechCocycle_diag R ι M hg i, sub_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The 2-cocycle relation, pointwise. -/
theorem cechTwoCocycle_rel {h : cechC2 ι M}
    (hh : h ∈ LinearMap.ker (cechD2 R ι M)) (i j k l : ι) :
    h j k l - h i k l + h i j l - h i j k = 0 := by
  simpa using
    congrFun (congrFun (congrFun (congrFun (LinearMap.mem_ker.mp hh) i) j) k) l

/-! ### The vanishing theorem: exactness of the full-nerve complex -/

/-- **Every 1-cocycle is a 1-coboundary** (`ker d¹ ≤ im d⁰`), over any
nonempty index type: the explicit primitive of a cocycle `g` is
`f i = g i₀ i` for any basepoint `i₀`, by the cocycle relation on the
triangle `(i₀, i, j)`.  This is the heart of the acyclicity of the
full nerve. -/
theorem cechD1_ker_le_range [Nonempty ι] :
    LinearMap.ker (cechD1 R ι M) ≤ LinearMap.range (cechD0 R ι M) := by
  intro g hg
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨fun i => g i₀ i, ?_⟩
  funext i j
  have h : g i j - (g i₀ j - g i₀ i) = 0 := by
    calc g i j - (g i₀ j - g i₀ i)
        = g i j - g i₀ j + g i₀ i := by abel
      _ = 0 := cechCocycle_rel R ι M hg i₀ i j
  simp only [cechD0_apply]
  exact (eq_of_sub_eq_zero h).symm

/-- **Exactness at `C¹`**: `ker d¹ = im d⁰` over a nonempty index
type.  Both inclusions: cocycles have primitives, coboundaries are
cocycles. -/
theorem cechD1_ker_eq_range [Nonempty ι] :
    LinearMap.ker (cechD1 R ι M) = LinearMap.range (cechD0 R ι M) :=
  le_antisymm (cechD1_ker_le_range R ι M) (cechD0_range_le_ker R ι M)

/-- Restatement without submodules: every 1-cocycle has an explicit
0-cochain primitive. -/
theorem cechCocycle_isCoboundary [Nonempty ι] {g : cechC1 ι M}
    (hg : cechD1 R ι M g = 0) : ∃ f : cechC0 ι M, cechD0 R ι M f = g :=
  cechD1_ker_le_range R ι M (LinearMap.mem_ker.mpr hg)

/-- Every 2-cocycle is a 2-coboundary (`ker d² ≤ im d¹`), by the same
basepoint primitive one degree up: `g i j = h i₀ i j`. -/
theorem cechD2_ker_le_range [Nonempty ι] :
    LinearMap.ker (cechD2 R ι M) ≤ LinearMap.range (cechD1 R ι M) := by
  intro h hh
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨fun i j => h i₀ i j, ?_⟩
  funext i j k
  have h' : h i j k - (h i₀ j k - h i₀ i k + h i₀ i j) = 0 := by
    calc h i j k - (h i₀ j k - h i₀ i k + h i₀ i j)
        = h i j k - h i₀ j k + h i₀ i k - h i₀ i j := by abel
      _ = 0 := cechTwoCocycle_rel R ι M hh i₀ i j k
  simp only [cechD1_apply]
  exact (eq_of_sub_eq_zero h').symm

/-- **Exactness at `C²`**: `ker d² = im d¹` over a nonempty index
type. -/
theorem cechD2_ker_eq_range [Nonempty ι] :
    LinearMap.ker (cechD2 R ι M) = LinearMap.range (cechD1 R ι M) :=
  le_antisymm (cechD2_ker_le_range R ι M) (cechD1_range_le_ker R ι M)

/-- Over a nonempty index type the 1-coboundaries exhaust the
1-cocycles: the coboundary submodule of `ker d¹` is everything. -/
theorem cechCoboundaries1_eq_top [Nonempty ι] :
    cechCoboundaries1 R ι M = ⊤ :=
  Submodule.eq_top_iff'.mpr fun g =>
    Submodule.mem_comap.mpr (cechD1_ker_le_range R ι M g.2)

/-- Likewise one degree up. -/
theorem cechCoboundaries2_eq_top [Nonempty ι] :
    cechCoboundaries2 R ι M = ⊤ :=
  Submodule.eq_top_iff'.mpr fun h =>
    Submodule.mem_comap.mpr (cechD2_ker_le_range R ι M h.2)

/-- **The vanishing theorem `Ȟ¹ = 0`**: for constant coefficients on
the full nerve of a cover with nonempty index type — in particular any
nonempty finite cover — the first Čech cohomology module is trivial.
The full nerve is a simplex, and a simplex is acyclic. -/
theorem cechH1_subsingleton [Nonempty ι] : Subsingleton (cechH1 R ι M) :=
  Submodule.Quotient.subsingleton_iff.mpr (cechCoboundaries1_eq_top R ι M)

/-- **`Ȟ² = 0`** as well: acyclicity continues one degree up. -/
theorem cechH2_subsingleton [Nonempty ι] : Subsingleton (cechH2 R ι M) :=
  Submodule.Quotient.subsingleton_iff.mpr (cechCoboundaries2_eq_top R ι M)

/-! ### `Ȟ⁰` is the coefficients -/

/-- A constant 0-cochain has vanishing coboundary. -/
@[simp] theorem cechD0_const (m : M) :
    cechD0 R ι M (fun _ => m) = 0 := by
  funext i j
  simp

/-- **`Ȟ⁰ ≃ M`**: evaluation at any basepoint is an `R`-linear
equivalence from the module of 0-cocycles to the coefficients — a
0-cocycle has all overlap discrepancies zero, so it is constant, and
its constant value determines it.  The linearized global-sections
module of the constant presheaf on a connected (full) nerve is exactly
`M`. -/
def cechH0EquivCoeff (i₀ : ι) : cechH0 R ι M ≃ₗ[R] M where
  toFun f := (f : cechC0 ι M) i₀
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun m := ⟨fun _ => m, LinearMap.mem_ker.mpr (cechD0_const R ι M m)⟩
  left_inv f := by
    refine Subtype.ext (funext fun i => ?_)
    have h : (f : cechC0 ι M) i₀ - (f : cechC0 ι M) i = 0 := by
      simpa using congrFun (congrFun (LinearMap.mem_ker.mp f.2) i) i₀
    exact eq_of_sub_eq_zero h
  right_inv _ := rfl

end CechComplex

/-! ### The STE bridge: set-level gluing lands in the linearized `Ȟ⁰` -/

section Bridge

variable {V : Type*} {A : V → Type*} {J : Type*}
variable (R : Type*) [CommRing R]

/-- **Linearization of a global section**: a global assignment
`f : ∀ v, A v` becomes the constant Čech 0-cochain `j ↦ single f 1`
with coefficients in the free `R`-module on global assignments.  This
is the object-level piece of the Abramsky–Brandenburger linearization
functor applied to the section presheaf of `Ste.VariablePresheaf`. -/
noncomputable def globalZeroCochain (f : ∀ v, A v) : cechC0 J ((∀ v, A v) →₀ R) :=
  fun _ => Finsupp.single f 1

/-- The linearization of a global section is a 0-cocycle: constant
cochains have no overlap discrepancy.  Every global section is seen by
the linearized `Ȟ⁰`. -/
theorem globalZeroCochain_mem_cechH0 (f : ∀ v, A v) :
    globalZeroCochain (J := J) R f ∈ cechH0 R J ((∀ v, A v) →₀ R) :=
  LinearMap.mem_ker.mpr (cechD0_const R J _ (Finsupp.single f 1))

/-- Distinct global sections have distinct `Ȟ⁰` cocycles: the
linearization loses nothing (`single` is injective since `1 ≠ 0`). -/
theorem globalZeroCochain_injective [Nontrivial R] [Nonempty J] :
    Function.Injective
      (fun f : ∀ v, A v => globalZeroCochain (J := J) R f) := by
  intro f g h
  obtain ⟨j⟩ := ‹Nonempty J›
  exact Finsupp.single_left_injective one_ne_zero (congrFun h j)

/-- **Set-level gluing lands in the linearized `Ȟ⁰`**: a compatible
family over a cover that glues (`Ste.CechCover`) is realized by a
global section of the constraint whose linearization is a genuine
0-cocycle.  The set-level sheaf story embeds in the module-level
cochain complex. -/
theorem GluesCover.exists_cechH0 {T : Set (∀ v, A v)} {U : J → Set V}
    {s : ∀ j, ∀ v : (U j), A v} (h : GluesCover T U s) :
    ∃ f ∈ T, (∀ j, (U j).restrict f = s j) ∧
      globalZeroCochain (J := J) R f ∈ cechH0 R J ((∀ v, A v) →₀ R) := by
  obtain ⟨f, hfT, hres⟩ := h
  exact ⟨f, hfT, hres, globalZeroCochain_mem_cechH0 R f⟩

/-- When the cover-level Čech obstruction vanishes, EVERY compatible
family of local sections is seen by the linearized `Ȟ⁰`: it glues to a
global section whose linearization is a 0-cocycle restricting to the
family.  In particular this holds for every compatible family of a
rectangular constraint over any cover
(`rectangular_cechVanishesCover`). -/
theorem CompatibleFamily.exists_cechH0 {T : Set (∀ v, A v)}
    {U : J → Set V} {s : ∀ j, ∀ v : (U j), A v}
    (hvan : CechVanishesCover T U) (hs : CompatibleFamily T U s) :
    ∃ f ∈ T, (∀ j, (U j).restrict f = s j) ∧
      globalZeroCochain (J := J) R f ∈ cechH0 R J ((∀ v, A v) →₀ R) :=
  GluesCover.exists_cechH0 R (hvan s hs)

/-- Over a genuine cover of the variable set, the `Ȟ⁰` cocycle of a
glued family is unique: any two global assignments realizing the same
family have equal linearizations, via `glueCover_unique`. -/
theorem globalZeroCochain_glue_unique {U : J → Set V}
    (hcover : ∀ v, ∃ j, v ∈ U j) {s : ∀ j, ∀ v : (U j), A v}
    {f f' : ∀ v, A v} (hf : ∀ j, (U j).restrict f = s j)
    (hf' : ∀ j, (U j).restrict f' = s j) :
    globalZeroCochain (J := J) R f = globalZeroCochain (J := J) R f' := by
  rw [glueCover_unique hcover hf hf']

end Bridge

end STE
