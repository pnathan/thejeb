/-
The TWISTED (section-presheaf-valued) Čech complex, and where the
coupling obstruction really lives.

`Ste.CechComplex` built the linearized Čech complex with CONSTANT
coefficients and proved its `Ȟ¹` vanishes identically (the full nerve
is an acyclic simplex): constant coefficients cannot see the coupling.
This file builds the honest TWISTED complex of the
Abramsky–Mansfield–Barbosa program (`abramsky2012cohomology`, §3–4):
coefficients in the *linearized section presheaf*

  `F_R(W) = (localSections T W) →₀ R`

— the free `R`-module on the genuine local sections of the constraint
`T` over the variable context `W` (`Ste.VariablePresheaf`) — with the
genuine restriction maps `Finsupp.lmapDomain` along section
restriction, over an arbitrary cover `U : J → Set V`.

**The complex (all machine-checked, no `sorry`).**

* `sectionRes`/`twistedRes`: the presheaf restriction on sections and
  its linearization, functorial (`twistedRes_twistedRes`).
* `twistedC0/C1/C2`, `twistedD0/D1`: the twisted cochain modules on
  the full nerve and their coboundaries; `twisted_d1_comp_d0` proves
  `d¹ ∘ d⁰ = 0`, so `twistedH0 = ker d⁰` is the twisted `Ȟ⁰`, and the
  twisted `Ȟ¹` is carried by the pair (`ker d¹`,
  `twistedCoboundaries1 = im d⁰`), with `im d⁰ ≤ ker d¹`
  (`twistedD0_range_le_ker`) and triviality of the quotient expressed
  as `TwistedH1Trivial : im d⁰ = ⊤` — see the note there on why the
  literal quotient TYPE is not formed (a `HasQuotient` typeclass
  diamond on submodule coercions of these concrete coefficient
  modules).
* `familyCochain_mem_twistedH0`: every set-level compatible family of
  local sections (`Ste.CechCover`) yields, via point masses, a twisted
  0-COCYCLE — an element of `Ȟ⁰(U, F_R)`.  This is Prop. 3.2 of
  `abramsky2012cohomology` in the STE setting.
* `twistedGlobal`/`twistedGlobal_mem_twistedH0`: linearized global
  sections `(↥T) →₀ R` map into the twisted `Ȟ⁰` by restriction.

**The main results.**

1. *The AMB per-section obstruction DEGENERATES in STE — a structural
   false negative* (`amb_extension_always`).  AMB define, for a single
   section `s₁` over a context `C₁`, a class `γ(s₁) ∈ Ȟ¹(U, F_C̃₁)` of
   the relative presheaf, and prove (Prop. 4.2 of
   `abramsky2012cohomology`) that `γ(s₁) = 0` iff `s₁` extends to a
   compatible family of the LINEARIZED presheaf.  We prove that in STE
   this extension condition holds for EVERY section of EVERY
   constraint over EVERY cover: `localSections` only contains
   restrictions of global solutions, so the point masses of a global
   extension provide the compatible family.  Hence the vanishing
   condition characterizing `γ(s₁) = 0` is identically satisfied: the
   `Ȟ¹`-graded per-section obstruction of the AMB program cannot
   detect the STE coupling — not because the coupling is invisible,
   but because STE's section presheaf bakes global extendability into
   its stalks.  (We prove the extension condition itself; the LES
   construction of `γ` is not mechanized.)

2. *The obstruction that DOES fire lives one degree down, in the
   cokernel of `F_R(V) → Ȟ⁰(U, F_R)`*
   (`diagonal_mixed_cocycle_not_in_globalRange`).  The STE coupling
   obstruction is a FAMILY-level phenomenon: the stuck object is a
   compatible family, not a section.  Its point-mass cocycle is a
   class in the twisted `Ȟ⁰`; the family glues `R`-LINEARLY
   (`LinearlyGlues`) iff that class lifts to a linearized global
   section, iff the representative lies in the image submodule of
   `twistedGlobalToH0` (`linearlyGlues_iff_mem_range` — the
   representative-level rendering of "class `= 0` in the cokernel").
   For the two-bit coupling `diagonal` with its singleton cover, the
   mixed family's cocycle is NOT in that image over every nontrivial
   commutative ring (`mixedFamily_not_linearlyGlues`): no `R`-linear
   combination of the two diagonal global sections — negative and
   mixed coefficients allowed — restricts to the mixed point masses.
   This is strictly stronger than the set-level failure
   `diagonal_gluing_fails` (`Ste.VariablePresheaf`): even "negative
   probabilities" cannot resolve the STE coupling, in contrast with
   the AMB world where every no-signalling model has a global section
   over the signed reals (`abramsky2011sheaf`).  Rectangular
   constraints glue linearly over every cover
   (`rectangular_linearlyGlues`), and set-level gluing always implies
   linear gluing (`GluesCover.linearlyGlues`), so nonmembership is a
   genuine obstruction invariant:
   `diagonal_twisted_obstruction_detects` packages nonvanishing at
   the coupling.

**Honest boundary.**  What is NOT here: the relative presheaf
`F_C̃₁`, the long exact sequence, and the literal connecting map `γ` —
result 1 mechanizes the extension condition that AMB Prop. 4.2 proves
EQUIVALENT to `γ(s₁) = 0`, not the class itself.  Whether the twisted
`Ȟ¹ = ker d¹ ⧸ im d⁰` — carried here by the submodule pair, see
`TwistedH1Trivial` — vanishes for pairwise-disjoint covers (which
would make the degeneracy of result 1 an instance of a blanket
`Ȟ¹`-triviality) is stated as outlook, not proven.  No
quantitative "obstruction rank = representation blow-up" theorem is
claimed; the set-level counts are in `Ste.CechObstruction` and
`Ste.CouplingLowerBound`.

References: S. Abramsky, S. Mansfield, R. S. Barbosa, *The cohomology
of non-locality and contextuality*, QPL 2011, EPTCS 95 (2012) 1–14
(`abramsky2012cohomology`); S. Abramsky, A. Brandenburger, *The
sheaf-theoretic structure of non-locality and contextuality*, New J.
Phys. 13 (2011) 113036 (`abramsky2011sheaf`); S. Abramsky, R. S.
Barbosa, K. Kishida, R. Lal, S. Mansfield, *Contextuality, cohomology
and paradox*, CSL 2015 (`abramsky2015paradox`).
-/
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Ste.CechComplex

namespace STE

noncomputable section

open Set

variable {V : Type*} {A : V → Type*} {J : Type*}

/-! ### The section presheaf on subtypes and its linearization -/

/-- **Presheaf restriction on local sections**: a local section of `T`
over `W` restricts, along `W' ⊆ W`, to a local section over `W'` —
the restriction of an extendable partial assignment is extendable via
the same global witness. -/
def sectionRes (T : Set (∀ v, A v)) {W W' : Set V} (h : W' ⊆ W)
    (s : ↥(localSections T W)) : ↥(localSections T W') :=
  ⟨Set.restrict₂ h s.1,
    Exists.elim s.2 fun g hg =>
      ⟨g, hg.1, by rw [← hg.2]; exact (congrFun (Set.restrict₂_comp_restrict h) g).symm⟩⟩

@[simp] theorem sectionRes_coe (T : Set (∀ v, A v)) {W W' : Set V}
    (h : W' ⊆ W) (s : ↥(localSections T W)) :
    (sectionRes T h s : ∀ v : W', A v) = Set.restrict₂ h s.1 := rfl

variable (R : Type*) [CommRing R]

/-- **The linearized section presheaf** `F_R(W)`: the free `R`-module
on the local sections of `T` over `W` — the coefficient system of the
twisted Čech complex (the linearization functor `F_R` of
`abramsky2012cohomology`, §4, applied to `localSections`). -/
abbrev twistedCoeff (T : Set (∀ v, A v)) (W : Set V) :=
  ↥(localSections T W) →₀ R

/-- The linearized restriction map `F_R(W) →ₗ F_R(W')`: pushforward of
formal `R`-combinations of sections along `sectionRes`. -/
def twistedRes (T : Set (∀ v, A v)) {W W' : Set V} (h : W' ⊆ W) :
    twistedCoeff R T W →ₗ[R] twistedCoeff R T W' :=
  Finsupp.lmapDomain R R (sectionRes T h)

theorem twistedRes_apply (T : Set (∀ v, A v)) {W W' : Set V}
    (h : W' ⊆ W) (φ : twistedCoeff R T W) :
    twistedRes R T h φ = Finsupp.mapDomain (sectionRes T h) φ := rfl

/-- The linearized restriction of a point mass is the point mass of
the restricted section. -/
theorem twistedRes_single (T : Set (∀ v, A v)) {W W' : Set V}
    (h : W' ⊆ W) (σ : ↥(localSections T W)) (r : R) :
    twistedRes R T h (Finsupp.single σ r) =
      Finsupp.single (sectionRes T h σ) r :=
  Finsupp.mapDomain_single

/-- **Functoriality of the linearized restriction**: restricting in
two steps is restricting along the composite inclusion.  This is the
presheaf law that makes the twisted coboundaries compose to zero. -/
theorem twistedRes_twistedRes (T : Set (∀ v, A v)) {W W' W'' : Set V}
    (h₁ : W'' ⊆ W') (h₂ : W' ⊆ W) (φ : twistedCoeff R T W) :
    twistedRes R T h₁ (twistedRes R T h₂ φ) =
      twistedRes R T (h₁.trans h₂) φ := by
  simp only [twistedRes_apply, ← Finsupp.mapDomain_comp]
  rfl

variable (T : Set (∀ v, A v)) (U : J → Set V)

/-! ### The twisted cochain modules and coboundaries -/

/-- Twisted 0-cochains: one element of the free module on the local
sections of each context. -/
abbrev twistedC0 := ∀ j, twistedCoeff R T (U j)

/-- Twisted 1-cochains: coefficients in the sections over each
pairwise overlap (full nerve, non-alternating presentation). -/
abbrev twistedC1 := ∀ j k, twistedCoeff R T (U j ∩ U k)

/-- Twisted 2-cochains: coefficients in the sections over each triple
overlap. -/
abbrev twistedC2 := ∀ j k l, twistedCoeff R T (U j ∩ U k ∩ U l)

/-- **The twisted degree-0 coboundary**
`(d⁰φ) j k = φ k |_{jk} - φ j |_{jk}`: the discrepancy of the
linearized local data on the overlap, computed with the GENUINE
presheaf restriction maps — this is where the twisted complex departs
from the constant-coefficient complex of `Ste.CechComplex`. -/
def twistedD0 : twistedC0 R T U →ₗ[R] twistedC1 R T U where
  toFun φ := fun j k =>
    twistedRes R T (Set.inter_subset_right : U j ∩ U k ⊆ U k) (φ k)
      - twistedRes R T (Set.inter_subset_left : U j ∩ U k ⊆ U j) (φ j)
  map_add' φ ψ := by
    funext j k
    simp only [Pi.add_apply, map_add]
    abel
  map_smul' r φ := by
    funext j k
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_sub]

@[simp] theorem twistedD0_apply (φ : twistedC0 R T U) (j k : J) :
    twistedD0 R T U φ j k =
      twistedRes R T (Set.inter_subset_right : U j ∩ U k ⊆ U k) (φ k)
        - twistedRes R T (Set.inter_subset_left : U j ∩ U k ⊆ U j) (φ j) := rfl

/-- Triple overlaps sit inside the left pairwise overlap. -/
theorem tripleInter_subset_left (j k l : J) :
    U j ∩ U k ∩ U l ⊆ U j ∩ U k := Set.inter_subset_left

/-- Triple overlaps sit inside the outer pairwise overlap. -/
theorem tripleInter_subset_mid (j k l : J) :
    U j ∩ U k ∩ U l ⊆ U j ∩ U l := fun _ hv => ⟨hv.1.1, hv.2⟩

/-- Triple overlaps sit inside the right pairwise overlap. -/
theorem tripleInter_subset_right (j k l : J) :
    U j ∩ U k ∩ U l ⊆ U k ∩ U l := fun _ hv => ⟨hv.1.2, hv.2⟩

/-- **The twisted degree-1 coboundary**: the alternating sum of the
restrictions of the three faces of the triangle `(j, k, l)` to the
triple overlap. -/
def twistedD1 : twistedC1 R T U →ₗ[R] twistedC2 R T U where
  toFun g := fun j k l =>
    twistedRes R T (tripleInter_subset_right U j k l) (g k l)
      - twistedRes R T (tripleInter_subset_mid U j k l) (g j l)
      + twistedRes R T (tripleInter_subset_left U j k l) (g j k)
  map_add' g₁ g₂ := by
    funext j k l
    simp only [Pi.add_apply, map_add]
    abel
  map_smul' r g := by
    funext j k l
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_sub, smul_add]

@[simp] theorem twistedD1_apply (g : twistedC1 R T U) (j k l : J) :
    twistedD1 R T U g j k l =
      twistedRes R T (tripleInter_subset_right U j k l) (g k l)
        - twistedRes R T (tripleInter_subset_mid U j k l) (g j l)
        + twistedRes R T (tripleInter_subset_left U j k l) (g j k) := rfl

/-- **The twisted cochain-complex identity** `d¹ ∘ d⁰ = 0`: the six
doubly-restricted terms cancel in pairs after functoriality collapses
each to a single restriction to the triple overlap (Prop. 3.1 of
`abramsky2012cohomology` for this presheaf). -/
theorem twisted_d1_comp_d0 :
    (twistedD1 R T U).comp (twistedD0 R T U) = 0 := by
  refine LinearMap.ext fun φ => ?_
  funext j k l
  simp only [LinearMap.comp_apply, twistedD1_apply, twistedD0_apply, map_sub,
    twistedRes_twistedRes, LinearMap.zero_apply, Pi.zero_apply]
  abel

/-- Twisted 1-coboundaries are twisted 1-cocycles. -/
theorem twistedD0_range_le_ker :
    LinearMap.range (twistedD0 R T U) ≤ LinearMap.ker (twistedD1 R T U) :=
  LinearMap.range_le_ker_iff.mpr (twisted_d1_comp_d0 R T U)

/-! ### Twisted cohomology as `R`-modules -/

/-- **The twisted `Ȟ⁰`**: the module of twisted 0-cocycles — families
of linearized local data agreeing on all overlaps under the genuine
restriction maps (Prop. 3.2 of `abramsky2012cohomology`: compatible
families of the linearized presheaf). -/
abbrev twistedH0 : Submodule R (twistedC0 R T U) :=
  LinearMap.ker (twistedD0 R T U)

/-- The twisted 1-coboundaries inside the twisted 1-cocycles. -/
def twistedCoboundaries1 : Submodule R (LinearMap.ker (twistedD1 R T U)) :=
  (LinearMap.range (twistedD0 R T U)).comap
    (LinearMap.ker (twistedD1 R T U)).subtype

/-- **Twisted `Ȟ¹`-triviality, submodule form**: the twisted
1-coboundaries exhaust the twisted 1-cocycles — equivalently, the
quotient `Ȟ¹ = ker d¹ ⧸ im d⁰` would be the zero module.  The
cohomology is carried by the pair (`LinearMap.ker (twistedD1)`,
`twistedCoboundaries1`); the literal quotient TYPE is not formed
because `Submodule` quotients over the submodule-coercion
`↥(ker d¹)` fail typeclass synthesis (`HasQuotient`) for these
concrete `Finsupp`/`Pi` coefficient modules — a diamond on the
derived `AddCommGroup`/`Module` instances, verified by CI diagnostics;
the submodule-level formulation is mathematically equivalent and
diamond-free.  Whether this triviality holds for pairwise-disjoint
covers (as its constant-coefficient shadow `cechH1_subsingleton`
does) is left OPEN here. -/
def TwistedH1Trivial : Prop := twistedCoboundaries1 R T U = ⊤

/-! ### Compatible families land in the twisted `Ȟ⁰` -/

/-- The point-mass 0-cochain of a family of local sections: the
Dirac lift of set-level data into the linearized complex. -/
def familyCochain {s : ∀ j, ∀ v : (U j), A v}
    (hsec : ∀ j, s j ∈ localSections T (U j)) : twistedC0 R T U :=
  fun j => Finsupp.single ⟨s j, hsec j⟩ 1

@[simp] theorem familyCochain_apply {s : ∀ j, ∀ v : (U j), A v}
    (hsec : ∀ j, s j ∈ localSections T (U j)) (j : J) :
    familyCochain R T U hsec j = Finsupp.single ⟨s j, hsec j⟩ 1 := rfl

/-- The two restrictions of a compatible family's sections to an
overlap agree, as elements of the section subtype. -/
theorem sectionRes_familyCompatible {s : ∀ j, ∀ v : (U j), A v}
    (hs : CompatibleFamily T U s) (j k : J) :
    sectionRes T (Set.inter_subset_right : U j ∩ U k ⊆ U k) ⟨s k, hs.1 k⟩
      = sectionRes T (Set.inter_subset_left : U j ∩ U k ⊆ U j)
          ⟨s j, hs.1 j⟩ := by
  refine Subtype.ext (funext fun v => ?_)
  exact (hs.2 j k v.1 v.2.1 v.2.2).symm

/-- **Compatible families are twisted 0-cocycles**: the point-mass
cochain of any set-level compatible family (`Ste.CechCover`) lies in
the twisted `Ȟ⁰` — its overlap discrepancies vanish because the
underlying sections genuinely agree on overlaps.  Set-level
compatibility embeds in the linearized cohomology at degree zero. -/
theorem familyCochain_mem_twistedH0 {s : ∀ j, ∀ v : (U j), A v}
    (hs : CompatibleFamily T U s) :
    familyCochain R T U hs.1 ∈ twistedH0 R T U :=
  LinearMap.mem_ker.mpr (by
    funext j k
    simp only [twistedD0_apply, familyCochain_apply, twistedRes_single,
      sectionRes_familyCompatible T U hs j k, sub_self, Pi.zero_apply])

/-! ### Linearized global sections and the gluing question -/

/-- A global solution of `T` restricts to a local section over each
context: the section-valued global-to-local map. -/
def globalToSection (j : J) : ↥T → ↥(localSections T (U j)) := fun g =>
  ⟨(U j).restrict g.1, restrict_mem_localSections _ g.2⟩

/-- **The linearized global-to-local map**
`F_R(V) = (↥T →₀ R) →ₗ C⁰`: pushforward of formal `R`-combinations of
global solutions to their restriction point masses in every
context. -/
def twistedGlobal : (↥T →₀ R) →ₗ[R] twistedC0 R T U :=
  LinearMap.pi fun j => Finsupp.lmapDomain R R (globalToSection T U j)

theorem twistedGlobal_apply (φ : ↥T →₀ R) (j : J) :
    twistedGlobal R T U φ j =
      Finsupp.mapDomain (globalToSection T U j) φ := rfl

/-- Linearized global sections are twisted 0-cocycles: the two
restriction routes to an overlap agree on global data.  The map
`F_R(V) → Ȟ⁰(U, F_R)` of the twisted complex. -/
theorem twistedGlobal_mem_twistedH0 (φ : ↥T →₀ R) :
    twistedGlobal R T U φ ∈ twistedH0 R T U :=
  LinearMap.mem_ker.mpr (by
    funext j k
    simp only [twistedD0_apply, twistedGlobal_apply, twistedRes_apply,
      ← Finsupp.mapDomain_comp, Pi.zero_apply]
    rw [sub_eq_zero]
    rfl)

/-- **`R`-linear gluing**: the point-mass cocycle of a family of local
sections lifts along `F_R(V) → Ȟ⁰(U, F_R)` — some formal `R`-linear
combination of GLOBAL solutions restricts to exactly the family's
point masses in every context.  Set-level gluing is the special case
of a single point mass; negative and mixed coefficients make this a
strictly weaker requirement in general — this is precisely the slack
that produces the AMB false negatives. -/
def LinearlyGlues {s : ∀ j, ∀ v : (U j), A v}
    (hsec : ∀ j, s j ∈ localSections T (U j)) : Prop :=
  familyCochain R T U hsec ∈ LinearMap.range (twistedGlobal R T U)

/-- Set-level gluing implies `R`-linear gluing: the glue's point mass
is the lift. -/
theorem GluesCover.linearlyGlues {s : ∀ j, ∀ v : (U j), A v}
    (hs : CompatibleFamily T U s) (hg : GluesCover T U s) :
    LinearlyGlues R T U hs.1 := by
  obtain ⟨f, hfT, hres⟩ := hg
  refine LinearMap.mem_range.mpr ⟨Finsupp.single ⟨f, hfT⟩ 1, ?_⟩
  funext j
  rw [twistedGlobal_apply, Finsupp.mapDomain_single, familyCochain_apply]
  exact congrArg (fun σ => Finsupp.single σ (1 : R)) (Subtype.ext (hres j))

/-! ### Result 1: the AMB per-section obstruction degenerates in STE -/

/-- **The AMB extension condition holds for EVERY local section in
STE** — the structural false negative.  For any constraint `T`, any
cover `U`, any context `j₁`, and any local section `s₁` over `U j₁`,
there is a twisted 0-cocycle `r` (a compatible family of the
LINEARIZED presheaf) whose `j₁`-component is exactly the point mass of
`s₁`.  By Prop. 4.2 of `abramsky2012cohomology` this extension
condition is equivalent to the vanishing of the relative-cohomology
obstruction `γ(s₁) ∈ Ȟ¹(U, F_C̃₁)`; since STE's `localSections` only
contains restrictions of GLOBAL solutions, the extension always exists
— take the point masses of any global witness — and the per-section
cohomological obstruction of the AMB program is identically zero on
STE section presheaves.  The `Ȟ¹`-graded obstruction cannot locate the
coupling; contrast `mixedFamily_not_linearlyGlues`, where the
family-level `Ȟ⁰`-cokernel class fires. -/
theorem amb_extension_always (j₁ : J) (s₁ : ↥(localSections T (U j₁))) :
    ∃ r ∈ twistedH0 R T U, r j₁ = Finsupp.single s₁ 1 := by
  obtain ⟨g, hg, hgs⟩ := s₁.2
  refine ⟨twistedGlobal R T U (Finsupp.single ⟨g, hg⟩ 1),
    twistedGlobal_mem_twistedH0 R T U _, ?_⟩
  rw [twistedGlobal_apply, Finsupp.mapDomain_single]
  exact congrArg (fun σ => Finsupp.single σ (1 : R)) (Subtype.ext hgs)

/-! ### Result 2: the obstruction class in `coker(F_R(V) → Ȟ⁰)` -/

/-- The linearized global-to-local map, corestricted to the twisted
`Ȟ⁰` it lands in. -/
def twistedGlobalToH0 : (↥T →₀ R) →ₗ[R] ↥(twistedH0 R T U) :=
  LinearMap.codRestrict (twistedH0 R T U) (twistedGlobal R T U)
    (twistedGlobal_mem_twistedH0 R T U)

/-- **The cokernel obstruction, representative form.**  The class of a
compatible family's point-mass cocycle in the cokernel
`Ȟ⁰(U, F_R) ⧸ im F_R(V)` is zero iff the representative lies in the
image submodule `LinearMap.range (twistedGlobalToH0 R T U)` — which is
exactly `R`-linear gluability.  (The literal quotient module hits the
same `HasQuotient` typeclass diamond as the twisted `Ȟ¹`, see
`TwistedH1Trivial`; membership of the
representative in the image submodule is the equivalent, diamond-free
rendering of `[cocycle] = 0` in the cokernel.) -/
theorem linearlyGlues_iff_mem_range {s : ∀ j, ∀ v : (U j), A v}
    (hs : CompatibleFamily T U s) :
    LinearlyGlues R T U hs.1 ↔
      (⟨familyCochain R T U hs.1, familyCochain_mem_twistedH0 R T U hs⟩ :
          ↥(twistedH0 R T U)) ∈
        LinearMap.range (twistedGlobalToH0 R T U) := by
  constructor
  · intro h
    obtain ⟨φ, hφ⟩ := LinearMap.mem_range.mp h
    exact LinearMap.mem_range.mpr ⟨φ, Subtype.ext hφ⟩
  · intro h
    obtain ⟨φ, hφ⟩ := LinearMap.mem_range.mp h
    exact LinearMap.mem_range.mpr ⟨φ, congrArg Subtype.val hφ⟩

/-- **Rectangular constraints glue linearly over every cover**: their
compatible families glue set-theoretically
(`rectangular_cechVanishesCover`), hence linearly — the cokernel class
of every compatible family of a rectangle vanishes. -/
theorem rectangular_linearlyGlues (P : ∀ v, Set (A v))
    (hcover : ∀ v, ∃ j, v ∈ U j) {s : ∀ j, ∀ v : (U j), A v}
    (hs : CompatibleFamily (Set.univ.pi P) U s) :
    LinearlyGlues R (Set.univ.pi P) U hs.1 :=
  GluesCover.linearlyGlues R _ U hs
    (rectangular_cechVanishesCover P U hcover s hs)

/-! ### The computed instance: the two-bit coupling `diagonal` -/

/-- The singleton cover of the two-variable space, as a cover
function. -/
def twoCover : Fin 2 → Set (Fin 2) := fun v => {v}

/-- The mixed family of local sections of the coupling: `false` at
variable `0`, `true` at variable `1` — the stuck cocycle of
`diagonal_gluing_fails`, now as twisted-complex data. -/
def mixedFamily : ∀ j : Fin 2, ∀ v : (twoCover j), Bool :=
  fun j _ => decide (j = 1)

/-- The mixed family is a genuine compatible family of the coupling
over the singleton cover: each component is a local section (the
coupling's margins are full), and overlap agreement is vacuous since
distinct singletons are disjoint. -/
theorem mixedFamily_compatible :
    CompatibleFamily diagonal twoCover mixedFamily := by
  refine ⟨fun j => ?_, fun j k v hv hv' => ?_⟩
  · show mixedFamily j ∈ localSections diagonal ({j} : Set (Fin 2))
    rw [localSections_diagonal_singleton]
    exact Set.mem_univ _
  · have hj : v = j := hv
    have hk : v = k := hv'
    subst hj
    subst hk
    rfl

/-- The all-`true` global solution of the coupling. -/
def diagTrue : ↥diagonal := ⟨fun _ => true, rfl⟩

/-- A global solution of the coupling is a constant assignment. -/
theorem diagonal_apply_eq (g : ↥diagonal) (v w : Fin 2) :
    g.1 v = g.1 w := by
  have h : g.1 0 = g.1 1 := g.2
  fin_cases v <;> fin_cases w <;> first | rfl | exact h | exact h.symm

/-- Restriction to a single variable is injective on global solutions
of the coupling: a diagonal solution is determined by either
coordinate. -/
theorem globalToSection_diagonal_injective (j : Fin 2) :
    Function.Injective (globalToSection diagonal twoCover j) := by
  intro g g' h
  have hj : g.1 j = g'.1 j :=
    congrFun (congrArg Subtype.val h) ⟨j, rfl⟩
  refine Subtype.ext (funext fun v => ?_)
  calc g.1 v = g.1 j := diagonal_apply_eq g v j
    _ = g'.1 j := hj
    _ = g'.1 v := diagonal_apply_eq g' j v

/-- **The coupling does not glue `R`-linearly — the twisted `Ȟ⁰`
obstruction fires.**  No formal `R`-linear combination of the two
global solutions of `diagonal` restricts to the mixed family's point
masses: evaluating the required lift at the all-`true` solution forces
its coefficient to be `0` (from context `0`) and `1` (from context
`1`).  Over every nontrivial ring — negative, rational, real
coefficients included — the mixed family is not linearly explainable
by global data: the coupling is invisible to margins but NOT to the
twisted degree-0 cohomology.  Contrast `amb_extension_always`. -/
theorem mixedFamily_not_linearlyGlues [Nontrivial R] :
    ¬ LinearlyGlues R diagonal twoCover mixedFamily_compatible.1 := by
  intro h
  obtain ⟨φ, hφ⟩ := LinearMap.mem_range.mp h
  have h0 := congrFun hφ 0
  have h1 := congrFun hφ 1
  rw [twistedGlobal_apply, familyCochain_apply] at h0 h1
  -- context 0 pins the coefficient of the all-`true` solution to 0
  have hne : globalToSection diagonal twoCover 0 diagTrue ≠
      ⟨mixedFamily 0, mixedFamily_compatible.1 0⟩ := by
    intro heq
    have hval : (twoCover 0).restrict diagTrue.1 = mixedFamily 0 :=
      congrArg Subtype.val heq
    have hpt := congrFun hval ⟨0, rfl⟩
    exact absurd hpt (by decide)
  have e0 := DFunLike.congr_fun h0
    (globalToSection diagonal twoCover 0 diagTrue)
  rw [Finsupp.mapDomain_apply (globalToSection_diagonal_injective 0),
    Finsupp.single_eq_of_ne hne] at e0
  -- context 1 pins the same coefficient to 1
  have heq1 : globalToSection diagonal twoCover 1 diagTrue =
      ⟨mixedFamily 1, mixedFamily_compatible.1 1⟩ := by
    refine Subtype.ext (funext fun u => ?_)
    exact (by decide : (true : Bool) = decide ((1 : Fin 2) = 1))
  have e1 := DFunLike.congr_fun h1
    (globalToSection diagonal twoCover 1 diagTrue)
  rw [Finsupp.mapDomain_apply (globalToSection_diagonal_injective 1),
    heq1, Finsupp.single_eq_same] at e1
  exact one_ne_zero (e1.symm.trans e0)

/-- **The nonzero cokernel class at the coupling, representative
form**: the mixed family's point-mass cocycle is an element of the
twisted `Ȟ⁰` that does NOT lie in the image of the linearized global
sections — its class in `coker(F_R(V) → Ȟ⁰(U, F_R))` is nonzero over
every nontrivial commutative ring.  A genuine twisted-cohomology class
locates the STE coupling obstruction — at degree 0 (mod global
sections), where the per-section `Ȟ¹` obstruction of
`amb_extension_always` is structurally blind. -/
theorem diagonal_mixed_cocycle_not_in_globalRange [Nontrivial R] :
    (⟨familyCochain R diagonal twoCover mixedFamily_compatible.1,
        familyCochain_mem_twistedH0 R diagonal twoCover
          mixedFamily_compatible⟩ :
        ↥(twistedH0 R diagonal twoCover)) ∉
      LinearMap.range (twistedGlobalToH0 R diagonal twoCover) :=
  fun h => mixedFamily_not_linearlyGlues R
    ((linearlyGlues_iff_mem_range R diagonal twoCover
      mixedFamily_compatible).mpr h)

/-- **The twisted obstruction detects the coupling** (headline): the
mixed family of the two-bit coupling is set-level stuck AND fails even
`R`-linear gluing — the linearized degree-0 invariant sees exactly the
family that the set-level sheaf condition rejects, over every
nontrivial commutative ring. -/
theorem diagonal_twisted_obstruction_detects [Nontrivial R] :
    ¬ GluesCover diagonal twoCover mixedFamily ∧
      ¬ LinearlyGlues R diagonal twoCover mixedFamily_compatible.1 :=
  ⟨fun hg => mixedFamily_not_linearlyGlues R
      (GluesCover.linearlyGlues R diagonal twoCover
        mixedFamily_compatible hg),
    mixedFamily_not_linearlyGlues R⟩

end

end STE
