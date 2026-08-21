/-
Genuine Čech `Ȟ¹` nonvanishing over an overlapping cover: the
frustrated XOR triangle, with `ℤ` coefficients.

This file discharges the open item stated at the end of
`papers/notes/ste-cohomology-recast.tex` — "exhibit a constraint and an
overlapping cover whose twisted `H¹` is genuinely nonzero" — and is the
first genuine (overlapping-cover, `ℤ`-coefficient) first-cohomology
nonvanishing in this development.  Everything is machine-checked, no
`sorry`.

**The instance.**  Three Boolean variables `Fin 3`, the *pair cover*
`triangleCover i = {i, i+1}` — three contexts, each pairwise overlap a
NONEMPTY singleton `{k}`, triple overlap empty
(`triangleCover_overlap`, `triangleCover_tripleOverlap`).  This is the
nerve-of-a-cycle cover of the Abramsky–Mansfield–Barbosa contextuality
scenarios (`abramsky2012cohomology`).  On it, the XOR (parity) triangle
with frustration parameter `a : Fin 3 → Bool`: each patch `{i, i+1}`
carries the pair constraint `f i ⊕ f (i+1) = a i`.  The system is
*frustrated* when `a 0 ⊕ a 1 ⊕ a 2 = true` (`Frustrated`): each pair
constraint is separately satisfiable — every patch has exactly two
local solutions (`patchAssign`, `patchAssign_patchSolution`,
`PatchSolution.eq_patchAssign`) and every restriction to an overlap is
onto both values — but the global constraint set is EMPTY
(`xorTriangle_eq_empty_iff`), and no family of local solutions is even
pairwise compatible (`frustrated_not_modelCompatible`): the odd cycle
is strongly contextual in miniature.  This is the AvN (all-vs-nothing)
mechanism of the AMB program: an odd system of parity equations,
locally consistent, globally inconsistent (`abramsky2012cohomology`,
§5–6 — the PR box and GHZ computations are exactly odd XOR systems on
cycle-shaped covers; the AvN terminology is developed further in
`abramsky2015paradox`).

**Why this file builds its own complex.**  The STE section presheaf
`localSections T W` (`Ste.VariablePresheaf`) contains only restrictions
of GLOBAL solutions.  For the frustrated triangle `T = ∅`, so that
presheaf is empty over every context, its linearization is the zero
complex, and the library's twisted `Ȟ¹` over it is trivially trivial —
we PROVE this (`frustrated_twistedH1Trivial`, via the general
`twistedH1Trivial_of_empty`): the STE presheaf is structurally blind to
the frustrated model, for the same reason `amb_extension_always`
(`Ste.TwistedCech`) degenerates — global extendability is baked into
its stalks.  The honest coefficient system is the AMB *empirical
model*: local solution sets given by the LOCAL pair constraints, which
exist (two per patch) whether or not a global solution does.  We build
its linearized Čech complex concretely: patch-`i` solutions are coded
by their value at vertex `i` (faithfully — `patchAssign_low`,
`PatchSolution.eq_patchAssign`), so `C⁰ = Fin 3 → (Bool → ℤ)` (free
`ℤ`-module on the two solutions of each patch), `C¹ = Fin 3 → (Bool → ℤ)`
(free module on the two sections of each overlap vertex; edge `k` is
the overlap `{k+1}` of patches `k` and `k+1`), and `C² = Empty → ℤ = 0`
(the ordered nerve has no 2-simplex: the triple overlap is empty).  The
coboundary `modD0` uses the genuine restriction maps: patch `k+1`
restricts to its low vertex by the identity on codes, patch `k` to its
high vertex by `resHigh (a k)` (xor-translation of codes); `modD1 = 0`,
so `d¹ ∘ d⁰ = 0` (`modD1_comp_modD0`) and every 1-cochain is a cocycle
(`modD1_ker_eq_top`).

**Result 1 — plain `Ȟ¹ ≠ 0` over the overlapping cover**
(`triangle_modH1_nonvanishing`).  The nerve of the pair cover is a
CIRCLE, not a simplex, and the complex sees it: the total-coefficient
functional `totalSum` kills every coboundary (`totalSum_modD0` — the
telescoping around the cycle), while the explicit cocycle
`circleWitness` has total sum `1`.  So `ker d¹ ⊄ im d⁰`: for EVERY
parameter `a` (frustrated or not) the twisted `Ȟ¹` of this cover is
nonzero.  Contrast: for the disjoint singleton covers used everywhere
else in the library, `C¹` carries no data and `Ȟ¹ ≡ 0` structurally
(`TwistedH1Trivial` discussion in `Ste.TwistedCech`); and for constant
coefficients on the full nerve, `Ȟ¹ = 0` by acyclicity
(`cechH1_subsingleton`, `Ste.CechComplex`).  This class is TOPOLOGICAL
(it does not depend on frustration); the contextuality-detecting class
is Result 2.

**Result 2 — the AMB obstruction class detects frustration exactly**
(`twistedH1_nonvanishing_frustratedTriangle`,
`ambCocycle_mem_relCoboundaries_iff`).  Following
`abramsky2012cohomology` §4 (Prop. 4.1–4.2): fix the local solution
`s₁ = patchAssign a 0 false` on patch `0`, extend it — by overlap
agreement with `s₁` only, the no-signalling extension — to the family
coded by `ambCochain a = ![false, a 0, a 2]`
(`ambFamily_agrees_at_one`, `ambFamily_agrees_at_zero`), and form
`z := ambCocycle a = d⁰(ambCochain a)`.  Then:

* `z` is a RELATIVE cocycle for the relative presheaf `F̄_{U₀}`
  (kernel of restriction into patch `0`): its components at the two
  overlap vertices inside `U₀` vanish, and at vertex `2` (disjoint
  from `U₀`) its coefficient sum vanishes (`ambCocycle_mem_relC1` —
  AMB Prop. 4.1).  The relative cochain modules are mechanized
  concretely as the kernels they are: `relC1` (with `emptyRes`, the
  restriction to `F(∅) ≅ ℤ`), and `relC0`, which is `⊥` because all
  three relative restrictions are injective (`relC0_eq_bot`).
* When `Frustrated a`, `z` is NOT a relative coboundary — the class
  `γ(s₁) = [z] ∈ Ȟ¹(U, F̄_{U₀})` is nonzero; when unfrustrated, it is
  (`unfrustrated_ambCocycle_isCoboundary`): the invariant detects
  EXACTLY the obstruction, `z ∈ im d⁰|_rel ↔ ¬Frustrated a`
  (`ambCocycle_mem_relCoboundaries_iff`), because
  `z 1 = pt (a 2) - pt (a 0 ⊕ a 1)` (`ambCocycle_one`) — the
  frustration parity is literally the discrepancy of the two routes
  around the cycle to vertex `2`.

**Honest boundary.**  In the PLAIN (non-relative) complex the class of
`z` is zero — trivially, since `z = d⁰(ambCochain a)` by definition
(`ambCocycle` IS a plain coboundary); this is AMB's remark after
Prop. 4.1: `ambCochain a` is not a RELATIVE 0-cochain (its patch-0
component is the point mass of `s₁`, not `0`), which is exactly why
`[z]` can be nonzero relatively.  So the frustration-detecting
nonvanishing here is the relative (connecting-map) class of AMB §4,
computed concretely — not a plain-`Ȟ¹` class; the plain `Ȟ¹ ≠ 0` of
Result 1 is a cover-topology fact, indifferent to frustration.  The
statements are in the quotient-free submodule-pair house style of
`Ste.TwistedCech` (`TwistedH1Trivial`): "cocycle not in the coboundary
submodule", avoiding the known `HasQuotient` instance diamond.  The
general relative-presheaf functor and long exact sequence are still
not mechanized; what is mechanized is this instance, kernel conditions
and all, end to end.

References: S. Abramsky, S. Mansfield, R. S. Barbosa, *The cohomology
of non-locality and contextuality*, QPL 2011, EPTCS 95 (2012) 1–14
(`abramsky2012cohomology`) — §3 (Čech cohomology of a presheaf, the
nerve), §4 (the relative obstruction `γ(s)`, Props. 4.1–4.3), §5–6
(PR-box/GHZ/Kochen–Specker computations, all odd-parity/AvN-type);
S. Abramsky, R. S. Barbosa, K. Kishida, R. Lal, S. Mansfield,
*Contextuality, cohomology and paradox*, CSL 2015
(`abramsky2015paradox`) — AvN arguments and cohomological obstruction;
S. Abramsky, A. Brandenburger, *The sheaf-theoretic structure of
non-locality and contextuality*, New J. Phys. 13 (2011) 113036
(`abramsky2011sheaf`).
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Ste.TwistedCech

namespace STE

open Set

/-! ### The pair cover of the triangle -/

/-- **The pair (triangle) cover** of three variables: context `i` is the
pair `{i, i+1}` (indices mod 3).  Unlike the singleton covers used
elsewhere in this development, its pairwise overlaps are NONEMPTY
(`triangleCover_overlap`), so degree-1 Čech data is substantive; the
nerve is a cycle, not a simplex. -/
def triangleCover : Fin 3 → Set (Fin 3) := fun i => {i, i + 1}

/-- In `Fin 3`, no vertex is its own successor: the two ends of each
patch are distinct. -/
theorem fin3_add_one_ne (i : Fin 3) : i + 1 ≠ i := by revert i; decide

/-- The low vertex of patch `i` belongs to it. -/
theorem mem_low (i : Fin 3) : i ∈ triangleCover i := Or.inl rfl

/-- The high vertex of patch `i` belongs to it. -/
theorem mem_high (i : Fin 3) : i + 1 ∈ triangleCover i := Or.inr rfl

/-- The pair cover covers the variable set. -/
theorem triangleCover_covers (v : Fin 3) : ∃ i, v ∈ triangleCover i :=
  ⟨v, mem_low v⟩

/-- **The overlaps are nonempty singletons**: consecutive patches `k`
and `k+1` meet exactly in the vertex `k+1`.  This is what makes the
cover genuinely overlapping — the Čech compatibility condition and the
degree-1 cochain modules have real content here. -/
theorem triangleCover_overlap (k : Fin 3) :
    triangleCover k ∩ triangleCover (k + 1) = {k + 1} := by
  fin_cases k <;> · ext v; fin_cases v <;> simp [triangleCover]

/-- The triple overlap is empty: the (injective) nerve of the pair
cover has no 2-simplex — it is the circle.  This is why `modC2` below
is the zero module and every 1-cochain is a cocycle. -/
theorem triangleCover_tripleOverlap :
    triangleCover 0 ∩ triangleCover 1 ∩ triangleCover 2 = ∅ := by
  ext v; fin_cases v <;> simp [triangleCover]

/-! ### The XOR triangle and frustration -/

/-- **The XOR (parity) triangle**: the global constraint
`f i ⊕ f (i+1) = a i` for all three edges, with frustration parameter
`a`.  Each conjunct is the pair constraint supported on the patch
`triangleCover i`. -/
def xorTriangle (a : Fin 3 → Bool) : Set (Fin 3 → Bool) :=
  {f | ∀ i, Bool.xor (f i) (f (i + 1)) = a i}

/-- **Frustration**: the parity of the cycle is odd,
`a 0 ⊕ a 1 ⊕ a 2 = true`.  XOR-ing the three pair constraints
telescopes to this parity, so frustration is the exact global
solvability invariant (`xorTriangle_eq_empty_iff`). -/
def Frustrated (a : Fin 3 → Bool) : Prop :=
  Bool.xor (a 0) (Bool.xor (a 1) (a 2)) = true

instance (a : Fin 3 → Bool) : Decidable (Frustrated a) := by
  unfold Frustrated; infer_instance

/-- **The frustrated triangle has no global solutions — and only the
frustrated one.**  `xorTriangle a = ∅` iff the cycle parity is odd:
XOR-ing the three constraints around the cycle forces
`a 0 ⊕ a 1 ⊕ a 2 = false` on any solution; conversely with even parity
`![false, a 0, a 0 ⊕ a 1]` solves the system. -/
theorem xorTriangle_eq_empty_iff (a : Fin 3 → Bool) :
    xorTriangle a = ∅ ↔ Frustrated a := by
  constructor
  · intro h
    by_contra hn
    have hf : ![false, a 0, Bool.xor (a 0) (a 1)] ∈ xorTriangle a := by
      intro i
      fin_cases i <;>
        · revert hn
          unfold Frustrated
          cases h0 : a 0 <;> cases h1 : a 1 <;> cases h2 : a 2 <;>
            simp [h0, h1, h2]
    rw [h] at hf
    exact hf
  · intro h
    rw [Set.eq_empty_iff_forall_notMem]
    intro f hf
    have h0 := hf 0
    have h1 := hf 1
    have h2 := hf 2
    revert h
    unfold Frustrated
    rw [show ((0 : Fin 3) + 1) = 1 from rfl] at h0
    rw [show ((1 : Fin 3) + 1) = 2 from rfl] at h1
    rw [show ((2 : Fin 3) + 1) = 0 from rfl] at h2
    rw [← h0, ← h1, ← h2]
    cases f 0 <;> cases f 1 <;> cases f 2 <;> decide

/-! ### The local model: patch solutions and their Boolean coding -/

/-- **The two local solutions of patch `i`, coded by `Bool`**: the
partial assignment on `{i, i+1}` with value `b` at the low vertex `i`
and (forced by the pair constraint) `b ⊕ a i` at the high vertex.
These exist for EVERY `a`, frustrated or not — this is the local
solution set of the AMB empirical model, in contrast to the STE
`localSections (xorTriangle a)`, which is empty when frustrated. -/
def patchAssign (a : Fin 3 → Bool) (i : Fin 3) (b : Bool) :
    ∀ v : (triangleCover i), Bool :=
  fun v => if v.1 = i then b else Bool.xor b (a i)

@[simp] theorem patchAssign_low (a : Fin 3 → Bool) (i : Fin 3) (b : Bool) :
    patchAssign a i b ⟨i, mem_low i⟩ = b := by
  simp [patchAssign]

@[simp] theorem patchAssign_high (a : Fin 3 → Bool) (i : Fin 3) (b : Bool) :
    patchAssign a i b ⟨i + 1, mem_high i⟩ = Bool.xor b (a i) := by
  simp [patchAssign, fin3_add_one_ne i]

/-- A partial assignment on patch `i` solves its pair constraint. -/
def PatchSolution (a : Fin 3 → Bool) (i : Fin 3)
    (s : ∀ v : (triangleCover i), Bool) : Prop :=
  Bool.xor (s ⟨i, mem_low i⟩) (s ⟨i + 1, mem_high i⟩) = a i

/-- Every coded assignment solves its patch constraint. -/
theorem patchAssign_patchSolution (a : Fin 3 → Bool) (i : Fin 3)
    (b : Bool) : PatchSolution a i (patchAssign a i b) := by
  unfold PatchSolution
  rw [patchAssign_low, patchAssign_high]
  cases b <;> simp

/-- **The coding is complete**: every solution of patch `i` is the coded
assignment of its value at the low vertex.  So `Bool` faithfully
enumerates the patch's local solution set, and the free module
`Bool → ℤ` below is honestly the linearization of that set. -/
theorem PatchSolution.eq_patchAssign {a : Fin 3 → Bool} {i : Fin 3}
    {s : ∀ v : (triangleCover i), Bool} (h : PatchSolution a i s) :
    s = patchAssign a i (s ⟨i, mem_low i⟩) := by
  funext v
  obtain ⟨v, hv⟩ := v
  rcases hv with rfl | hv
  · simp [patchAssign]
  · have hv' : v = i + 1 := hv
    subst hv'
    rw [patchAssign_high]
    unfold PatchSolution at h
    revert h
    cases s ⟨i, mem_low i⟩ <;> cases s ⟨i + 1, mem_high i⟩ <;> simp

/-- Global solutions restrict to patch solutions: the model's
local-solution sets contain the STE `localSections` data (and strictly
more, when frustrated). -/
theorem mem_xorTriangle_patchSolution {a : Fin 3 → Bool}
    {f : Fin 3 → Bool} (hf : f ∈ xorTriangle a) (i : Fin 3) :
    PatchSolution a i ((triangleCover i).restrict f) :=
  hf i

/-- **Strong contextuality of the frustrated model, code form**: no
choice of one local solution per patch (coded by its low-vertex value
`b i`) is pairwise compatible — agreement at each overlap vertex `k+1`
demands `b k ⊕ a k = b (k+1)` (`modelCompatible_iff`), and XOR-ing
around the cycle contradicts odd parity.  Compare
`mixedFamily_compatible` (`Ste.TwistedCech`): over disjoint singleton
covers stuck families are still compatible; here, with genuine
overlaps, the frustrated model has NO compatible family at all. -/
def ModelCompatible (a : Fin 3 → Bool) (b : Fin 3 → Bool) : Prop :=
  ∀ k, Bool.xor (b k) (a k) = b (k + 1)

/-- Code-level compatibility is genuine agreement of the coded local
solutions on the overlap vertices. -/
theorem modelCompatible_iff (a b : Fin 3 → Bool) :
    ModelCompatible a b ↔
      ∀ k, patchAssign a k (b k) ⟨k + 1, mem_high k⟩ =
        patchAssign a (k + 1) (b (k + 1)) ⟨k + 1, mem_low (k + 1)⟩ := by
  unfold ModelCompatible
  simp only [patchAssign_high, patchAssign_low]

theorem frustrated_not_modelCompatible {a : Fin 3 → Bool}
    (h : Frustrated a) : ¬ ∃ b, ModelCompatible a b := by
  rintro ⟨b, hb⟩
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  rw [show ((0 : Fin 3) + 1) = 1 from rfl] at h0
  rw [show ((1 : Fin 3) + 1) = 2 from rfl] at h1
  rw [show ((2 : Fin 3) + 1) = 0 from rfl] at h2
  revert h
  unfold Frustrated
  rw [← h1, ← h0] at h2
  revert h2
  cases b 0 <;> cases a 0 <;> cases a 1 <;> cases a 2 <;> decide

/-! ### The STE presheaf is blind to the frustrated model -/

/-- The STE section presheaf of the empty constraint is empty over
every context: `localSections` only contains restrictions of global
solutions. -/
theorem localSections_empty {V : Type*} {A : V → Type*} (W : Set V) :
    localSections (∅ : Set (∀ v, A v)) W = ∅ :=
  Set.image_empty _

/-- **The library's twisted `Ȟ¹` is trivially trivial over an empty
constraint**: all coefficient modules of `Ste.TwistedCech`'s complex
are zero, so the coboundaries exhaust the cocycles for ANY cover.  This
is a degeneracy, not a computation. -/
theorem twistedH1Trivial_of_empty {V : Type*} {A : V → Type*} {J : Type*}
    (R : Type*) [CommRing R] (U : J → Set V) :
    TwistedH1Trivial R (∅ : Set (∀ v, A v)) U := by
  have hz : ∀ g : twistedC1 R (∅ : Set (∀ v, A v)) U, g = 0 := by
    intro g
    funext j k
    ext σ
    obtain ⟨f, hf, -⟩ := σ.2
    exact absurd hf (Set.notMem_empty f)
  unfold TwistedH1Trivial twistedCoboundaries1
  rw [Submodule.eq_top_iff']
  intro g
  rw [Submodule.mem_comap]
  exact ⟨0, by rw [map_zero]; exact (hz _).symm⟩

/-- **Why this file cannot reuse the library's twisted complex**: over
the frustrated triangle the STE section presheaf is empty, so
`Ste.TwistedCech`'s twisted `Ȟ¹` is trivially trivial even over the
genuinely overlapping pair cover.  The structural blindness of
`amb_extension_always` in its sharpest form: the presheaf that bakes
global extendability into its stalks carries no local data at all when
there is nothing global.  The nonvanishing below therefore lives in the
model-level (empirical) complex, built next. -/
theorem frustrated_twistedH1Trivial {a : Fin 3 → Bool}
    (h : Frustrated a) :
    TwistedH1Trivial ℤ (xorTriangle a) triangleCover := by
  rw [(xorTriangle_eq_empty_iff a).mpr h]
  exact twistedH1Trivial_of_empty ℤ triangleCover

/-! ### The linearized model complex over the pair cover

Coefficients: the free `ℤ`-module on the local solutions of each
simplex's support.  Patch `i`'s two solutions are coded by `Bool`
(value at the low vertex, `patchAssign`); the overlap `{k+1}` of
patches `k` and `k+1` (edge `k` of the nerve) has two sections, coded
by the value at `k+1`.  The triple overlap is empty
(`triangleCover_tripleOverlap`), so the ordered nerve has no 2-simplex
and `C²` is the empty product — the zero module. -/

/-- Twisted 0-cochains of the model: one element of the free module on
the two local solutions of each patch. -/
abbrev modC0 : Type := Fin 3 → Bool → ℤ

/-- Twisted 1-cochains: one element of the free module on the two
sections of each overlap vertex.  Edge `k` is the overlap `{k+1}` of
patches `k` and `k+1`. -/
abbrev modC1 : Type := Fin 3 → Bool → ℤ

/-- Twisted 2-cochains: the empty product over the (nonexistent)
2-simplices of the nerve — the zero module.  Justified by
`triangleCover_tripleOverlap`. -/
abbrev modC2 : Type := Empty → ℤ

/-- **The high restriction map**: patch `k`'s solution coded `b` has
value `b ⊕ a k` at its high vertex `k+1` (`patchAssign_high`), so the
linearized restriction to edge `k` pushes the code forward along
`xor · (a k)` — on function modules, precomposition with the same
involution. -/
def resHigh (c : Bool) : (Bool → ℤ) →ₗ[ℤ] (Bool → ℤ) where
  toFun φ := fun b => φ (Bool.xor b c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem resHigh_apply (c : Bool) (φ : Bool → ℤ) (b : Bool) :
    resHigh c φ b = φ (Bool.xor b c) := rfl

/-- The high restriction is injective (precomposition with an
involution): linearized restriction loses nothing here.  This is what
forces the relative `C⁰` to vanish (`relC0_eq_bot`). -/
theorem resHigh_eq_zero {c : Bool} {φ : Bool → ℤ}
    (h : resHigh c φ = 0) : φ = 0 := by
  funext b
  have hb := congrFun h (Bool.xor b c)
  simpa [Bool.xor_assoc] using hb

/-- **The twisted degree-0 coboundary of the model complex**: on edge
`k` (the overlap `{k+1}`), the discrepancy of the two incident patches'
data under the GENUINE restriction maps — patch `k+1` restricts to its
low vertex by the identity on codes (`patchAssign_low`), patch `k` to
its high vertex by `resHigh (a k)` (`patchAssign_high`). -/
def modD0 (a : Fin 3 → Bool) : modC0 →ₗ[ℤ] modC1 where
  toFun φ := fun k => φ (k + 1) - resHigh (a k) (φ k)
  map_add' φ ψ := by
    funext k b
    simp only [Pi.add_apply, map_add, Pi.sub_apply]
    ring
  map_smul' r φ := by
    funext k b
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Pi.sub_apply,
      smul_eq_mul]
    ring

@[simp] theorem modD0_apply (a : Fin 3 → Bool) (φ : modC0) (k : Fin 3) :
    modD0 a φ k = φ (k + 1) - resHigh (a k) (φ k) := rfl

/-- **The twisted degree-1 coboundary is the zero map**: there is no
2-simplex to map to (`triangleCover_tripleOverlap`), so `C² = 0`. -/
def modD1 : modC1 →ₗ[ℤ] modC2 := 0

/-- The cochain-complex identity `d¹ ∘ d⁰ = 0` for the model complex —
degenerately, since `d¹` maps into the zero module. -/
theorem modD1_comp_modD0 (a : Fin 3 → Bool) :
    modD1.comp (modD0 a) = 0 :=
  LinearMap.zero_comp _

/-- Every model 1-cochain is a 1-cocycle: the nerve of the pair cover
is a circle, so there is no degree-2 condition to satisfy. -/
theorem modD1_ker_eq_top : LinearMap.ker modD1 = ⊤ :=
  LinearMap.ker_zero

/-! ### Result 1: plain `Ȟ¹ ≠ 0` over the overlapping cover -/

/-- Point mass in the free module on `Bool`-coded sections. -/
def pt (x : Bool) : Bool → ℤ := fun b => if b = x then 1 else 0

@[simp] theorem pt_self (x : Bool) : pt x x = 1 := by simp [pt]

theorem pt_apply_ne {x b : Bool} (h : b ≠ x) : pt x b = 0 := by
  simp [pt, h]

/-- Point masses of distinct sections have nonzero difference:
evaluate at the first. -/
theorem pt_sub_pt_ne_zero {x y : Bool} (h : x ≠ y) : pt x - pt y ≠ 0 := by
  intro h0
  have hx := congrFun h0 x
  rw [Pi.sub_apply, pt_self, pt_apply_ne h, Pi.zero_apply] at hx
  omega

/-- The high restriction of a point mass is the point mass of the
xor-translated code — the linearization of `patchAssign_high`. -/
theorem resHigh_pt (c y : Bool) :
    resHigh c (pt y) = pt (Bool.xor y c) := by
  funext b
  cases b <;> cases c <;> cases y <;> simp [pt]

/-- The total-coefficient functional on 1-cochains: the sum of all six
matrix entries.  It kills every coboundary (`totalSum_modD0`) —
restriction maps preserve total coefficient mass and the cycle
telescopes — so it descends to the plain `Ȟ¹`. -/
def totalSum : modC1 →ₗ[ℤ] ℤ where
  toFun g := ∑ k, (g k false + g k true)
  map_add' g₁ g₂ := by
    simp only [Pi.add_apply, Fin.sum_univ_three]
    ring
  map_smul' r g := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Fin.sum_univ_three]
    ring

theorem totalSum_apply (g : modC1) :
    totalSum g = ∑ k, (g k false + g k true) := rfl

/-- **Coboundaries have zero total coefficient**: each restriction map
preserves the coefficient sum of its patch, and summing the
discrepancies around the cycle telescopes to zero. -/
theorem totalSum_modD0 (a : Fin 3 → Bool) (φ : modC0) :
    totalSum (modD0 a φ) = 0 := by
  simp only [totalSum_apply, modD0_apply, Pi.sub_apply, resHigh_apply,
    Fin.sum_univ_three,
    show ((0 : Fin 3) + 1) = 1 from rfl,
    show ((1 : Fin 3) + 1) = 2 from rfl,
    show ((2 : Fin 3) + 1) = 0 from rfl]
  cases h0 : a 0 <;> cases h1 : a 1 <;> cases h2 : a 2 <;>
    simp only [Bool.xor_false, Bool.xor_true, Bool.not_false,
      Bool.not_true] <;> ring

/-- An explicit 1-cocycle with total coefficient `1`: a single point
mass on edge `0`. -/
def circleWitness : modC1 := ![pt false, 0, 0]

theorem totalSum_circleWitness : totalSum circleWitness = 1 := by
  rw [totalSum_apply, Fin.sum_univ_three,
    show circleWitness 0 = pt false from rfl,
    show circleWitness 1 = 0 from rfl,
    show circleWitness 2 = 0 from rfl]
  simp [pt]

/-- **Plain `Ȟ¹` nonvanishing over the overlapping cover** — for EVERY
frustration parameter.  The nerve of the pair cover is a circle, and
the twisted complex of the model presheaf sees its topology: there is a
1-cocycle (`circleWitness`) that is no coboundary, because `totalSum`
vanishes on `im d⁰` but not on it.  This is the first genuine
`ker d¹ ⊄ im d⁰` in the development — contrast the disjoint-cover
`TwistedH1Trivial` (`Ste.TwistedCech`) and the constant-coefficient
acyclicity `cechH1_subsingleton` (`Ste.CechComplex`).  It is a
TOPOLOGICAL class (present frustrated or not); the
contextuality-detecting class is `twistedH1_nonvanishing_frustratedTriangle`. -/
theorem triangle_modH1_nonvanishing (a : Fin 3 → Bool) :
    ∃ z : modC1, z ∈ LinearMap.ker modD1 ∧
      z ∉ LinearMap.range (modD0 a) := by
  refine ⟨circleWitness, LinearMap.mem_ker.mpr rfl, ?_⟩
  rintro ⟨φ, hφ⟩
  have h1 : totalSum circleWitness = 1 := totalSum_circleWitness
  rw [← hφ, totalSum_modD0] at h1
  exact one_ne_zero h1.symm

/-! ### Result 2: the relative AMB obstruction class -/

/-- **The restriction to the empty context**: the model presheaf has
exactly one section over `∅` (the empty assignment), so `F(∅) ≅ ℤ` and
restriction from a vertex is the coefficient-sum map.  This is the map
whose kernel defines the relative coefficient module at vertex `2`, the
one vertex outside patch `0`. -/
def emptyRes : (Bool → ℤ) →ₗ[ℤ] ℤ where
  toFun φ := φ false + φ true
  map_add' φ ψ := by simp only [Pi.add_apply]; ring
  map_smul' r φ := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem emptyRes_apply (φ : Bool → ℤ) :
    emptyRes φ = φ false + φ true := rfl

@[simp] theorem emptyRes_pt (x : Bool) : emptyRes (pt x) = 1 := by
  cases x <;> simp [pt]

/-- **The relative 1-cochains** `C¹(U, F̄_{U₀})`, concretely: the kernel
of restriction of overlap data into patch `0 = {0, 1}`.  Edge `0`
(vertex `1`) and edge `2` (vertex `0`) lie inside `U₀` and their code
restriction is bijective, so the kernel condition is vanishing; edge
`1` (vertex `2`) is disjoint from `U₀`, so restriction lands in
`F(∅) ≅ ℤ` (`emptyRes`) and the kernel condition is zero coefficient
sum.  This is AMB's relative presheaf `F̄_{C₁}`
(`abramsky2012cohomology`, §3), mechanized for this instance. -/
def relC1 : Submodule ℤ modC1 where
  carrier := {g | g 0 = 0 ∧ g 2 = 0 ∧ emptyRes (g 1) = 0}
  add_mem' := by
    rintro g₁ g₂ ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [Pi.add_apply, map_add, h1, h1', h2, h2', h3, h3']
  zero_mem' := ⟨rfl, rfl, map_zero _⟩
  smul_mem' := by
    rintro r g ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · show (r • g) 0 = 0
      rw [Pi.smul_apply, h1, smul_zero]
    · show (r • g) 2 = 0
      rw [Pi.smul_apply, h2, smul_zero]
    · show emptyRes ((r • g) 1) = 0
      rw [Pi.smul_apply, map_smul, h3, smul_zero]

theorem mem_relC1 {g : modC1} :
    g ∈ relC1 ↔ g 0 = 0 ∧ g 2 = 0 ∧ emptyRes (g 1) = 0 := Iff.rfl

/-- **The relative 0-cochains** `C⁰(U, F̄_{U₀})`: the kernel of
restricting each patch's data into its overlap with patch `0`.  Patch
`0` overlaps itself fully; patch `1` meets `U₀` in vertex `1`, its low
vertex, where code restriction is the identity; patch `2` meets `U₀` in
vertex `0`, its high vertex, where restriction is `resHigh (a 2)`. -/
def relC0 (a : Fin 3 → Bool) : Submodule ℤ modC0 where
  carrier := {φ | φ 0 = 0 ∧ φ 1 = 0 ∧ resHigh (a 2) (φ 2) = 0}
  add_mem' := by
    rintro φ ψ ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [Pi.add_apply, map_add, h1, h1', h2, h2', h3, h3']
  zero_mem' := ⟨rfl, rfl, map_zero _⟩
  smul_mem' := by
    rintro r φ ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · show (r • φ) 0 = 0
      rw [Pi.smul_apply, h1, smul_zero]
    · show (r • φ) 1 = 0
      rw [Pi.smul_apply, h2, smul_zero]
    · show resHigh (a 2) ((r • φ) 2) = 0
      rw [Pi.smul_apply, map_smul, h3, smul_zero]

/-- **The relative 0-cochains vanish**: every relative restriction map
out of a patch is injective (a patch solution is determined by its
value at ANY of its vertices — the model is deterministic given one
coordinate), so all three kernel conditions force zero.  Hence the
relative coboundary submodule is `⊥`, and the relative class of a
cocycle is zero iff the cocycle itself is. -/
theorem relC0_eq_bot (a : Fin 3 → Bool) : relC0 a = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro φ ⟨h0, h1, h2⟩
  funext k
  fin_cases k
  · exact h0
  · exact h1
  · exact resHigh_eq_zero h2

/-! ### The AMB family and its connecting cocycle -/

/-- **The AMB no-signalling family for the section
`s₁ = patchAssign a 0 false`**, coded: patch `0` carries `s₁` itself
(code `false`); patch `1` carries the unique local solution agreeing
with `s₁` at their overlap vertex `1` (code `a 0`, the value of `s₁`
there); patch `2` carries the unique local solution agreeing with `s₁`
at vertex `0` (code `a 2`).  As in `abramsky2012cohomology` §4, the
family extends `s₁` by overlap agreement WITH `s₁` — around the cycle
the two extensions need not agree with each other, and their
discrepancy at vertex `2` is the obstruction. -/
def ambCochain (a : Fin 3 → Bool) : modC0 :=
  ![pt false, pt (a 0), pt (a 2)]

/-- The patch-`1` member of the family genuinely agrees with `s₁` at
their overlap vertex `1`. -/
theorem ambFamily_agrees_at_one (a : Fin 3 → Bool) :
    patchAssign a 1 (a 0) ⟨(1 : Fin 3), mem_low 1⟩ =
      patchAssign a 0 false ⟨(0 : Fin 3) + 1, mem_high 0⟩ := by
  rw [patchAssign_low, patchAssign_high]
  simp

/-- The patch-`2` member of the family genuinely agrees with `s₁` at
their overlap vertex `0`. -/
theorem ambFamily_agrees_at_zero (a : Fin 3 → Bool) :
    patchAssign a 2 (a 2) ⟨(2 : Fin 3) + 1, mem_high 2⟩ =
      patchAssign a 0 false ⟨(0 : Fin 3), mem_low 0⟩ := by
  rw [patchAssign_low, patchAssign_high]
  cases a 2 <;> simp

/-- **The connecting cocycle** `z = d⁰(ambCochain a)`: the coboundary,
in the FULL complex, of the point-mass family extending `s₁`.  It is a
plain coboundary by construction (AMB's remark after Prop. 4.1) — the
content is that it lies in the RELATIVE complex
(`ambCocycle_mem_relC1`), where `ambCochain` itself does not, so its
relative class can be (and, frustrated, is) nonzero. -/
def ambCocycle (a : Fin 3 → Bool) : modC1 :=
  modD0 a (ambCochain a)

/-- The connecting cocycle is a plain coboundary — by definition.  AMB,
remark after Prop. 4.1: "although `z = d⁰(c)`, it is not necessarily a
coboundary in `C¹(U, F̄_{C₁})`, since `c` is not a cochain in
`C⁰(U, F̄_{C₁})`". -/
theorem ambCocycle_eq_modD0 (a : Fin 3 → Bool) :
    ambCocycle a = modD0 a (ambCochain a) := rfl

/-- Edge `0` (vertex `1 ∈ U₀`): both routes restrict `s₁`'s data, so
the discrepancy vanishes. -/
theorem ambCocycle_zero (a : Fin 3 → Bool) : ambCocycle a 0 = 0 := by
  show ambCochain a (0 + 1) - resHigh (a 0) (ambCochain a 0) = 0
  rw [show ((0 : Fin 3) + 1) = 1 from rfl,
    show ambCochain a 1 = pt (a 0) from rfl,
    show ambCochain a 0 = pt false from rfl,
    resHigh_pt, Bool.false_xor, sub_self]

/-- Edge `2` (vertex `0 ∈ U₀`): likewise. -/
theorem ambCocycle_two (a : Fin 3 → Bool) : ambCocycle a 2 = 0 := by
  show ambCochain a (2 + 1) - resHigh (a 2) (ambCochain a 2) = 0
  rw [show ((2 : Fin 3) + 1) = 0 from rfl,
    show ambCochain a 0 = pt false from rfl,
    show ambCochain a 2 = pt (a 2) from rfl,
    resHigh_pt, Bool.xor_self, sub_self]

/-- **The obstruction lives on edge `1` (vertex `2`, outside `U₀`)**:
the discrepancy of the two routes around the cycle from `s₁` to vertex
`2` — via patch `1` the value `a 0 ⊕ a 1`, via patch `2` the value
`a 2`.  Their difference of point masses is the frustration parity made
flesh. -/
theorem ambCocycle_one (a : Fin 3 → Bool) :
    ambCocycle a 1 = pt (a 2) - pt (Bool.xor (a 0) (a 1)) := by
  show ambCochain a (1 + 1) - resHigh (a 1) (ambCochain a 1) =
    pt (a 2) - pt (Bool.xor (a 0) (a 1))
  rw [show ((1 : Fin 3) + 1) = 2 from rfl,
    show ambCochain a 2 = pt (a 2) from rfl,
    show ambCochain a 1 = pt (a 0) from rfl,
    resHigh_pt]

/-- **AMB Proposition 4.1 for this instance**: the connecting cocycle
is a RELATIVE cocycle — it vanishes on the overlaps inside `U₀`, and on
the remaining overlap its restriction to `F(∅)` (the coefficient sum)
vanishes.  (The degree-2 cocycle condition is automatic:
`modD1_ker_eq_top`.) -/
theorem ambCocycle_mem_relC1 (a : Fin 3 → Bool) :
    ambCocycle a ∈ relC1 := by
  refine ⟨ambCocycle_zero a, ambCocycle_two a, ?_⟩
  rw [ambCocycle_one, map_sub, emptyRes_pt, emptyRes_pt, sub_self]

/-- **The connecting cocycle is nonzero exactly at frustration**: its
only possibly-nonzero component is the vertex-`2` discrepancy
`pt (a 2) - pt (a 0 ⊕ a 1)`, which vanishes iff the cycle parity is
even. -/
theorem ambCocycle_ne_zero_iff (a : Fin 3 → Bool) :
    ambCocycle a ≠ 0 ↔ Frustrated a := by
  have hkey : (Bool.xor (a 0) (a 1) ≠ a 2) ↔ Frustrated a := by
    unfold Frustrated
    cases a 0 <;> cases a 1 <;> cases a 2 <;> decide
  constructor
  · intro hz
    by_contra hn
    apply hz
    have heq : a 2 = Bool.xor (a 0) (a 1) := by
      by_contra hne
      exact hn (hkey.mp fun h => hne h.symm)
    have h1 : ambCocycle a 1 = 0 := by
      rw [ambCocycle_one, ← heq, sub_self]
    funext k b
    fin_cases k
    · exact congrFun (ambCocycle_zero a) b
    · exact congrFun h1 b
    · exact congrFun (ambCocycle_two a) b
  · intro h hz
    have h1 : ambCocycle a 1 = 0 := congrFun hz 1
    rw [ambCocycle_one] at h1
    exact pt_sub_pt_ne_zero (fun he => (hkey.mpr h) he.symm) h1

/-- **The relative class of the connecting cocycle vanishes iff the
triangle is unfrustrated** — the invariant detects exactly the
obstruction.  Since the relative 0-cochains vanish (`relC0_eq_bot`),
the relative coboundary submodule is `⊥` and the class is zero iff the
representative is. -/
theorem ambCocycle_mem_relCoboundaries_iff (a : Fin 3 → Bool) :
    ambCocycle a ∈ Submodule.map (modD0 a) (relC0 a) ↔ ¬ Frustrated a := by
  rw [relC0_eq_bot, Submodule.map_bot, Submodule.mem_bot,
    ← not_iff_not, ← Ne, ambCocycle_ne_zero_iff, not_not]

/-- **The sanity companion**: for the UNfrustrated triangle the
connecting cocycle IS a relative coboundary (indeed zero) — no false
positive. -/
theorem unfrustrated_ambCocycle_isCoboundary {a : Fin 3 → Bool}
    (h : ¬ Frustrated a) :
    ambCocycle a ∈ Submodule.map (modD0 a) (relC0 a) :=
  (ambCocycle_mem_relCoboundaries_iff a).mpr h

/-- **THE HEADLINE — genuine twisted `Ȟ¹` nonvanishing at the
frustrated triangle** (submodule-pair form, house style of
`Ste.TwistedCech`): over the genuinely overlapping pair cover with `ℤ`
coefficients, the connecting cocycle of the local section
`s₁ = patchAssign a 0 false` is a 1-cocycle of the relative complex
`C•(U, F̄_{U₀})` that is NOT a relative coboundary — the AMB obstruction
class `γ(s₁) ∈ Ȟ¹(U, F̄_{U₀})` is nonzero (`abramsky2012cohomology`,
§4, Props. 4.1–4.2; nonvanishing instances §5–6).  With
`ambCocycle_mem_relCoboundaries_iff` and
`triangle_modH1_nonvanishing`, this is the first genuine
first-cohomology obstruction computed in this development: the
frustration parity `a 0 ⊕ a 1 ⊕ a 2 = true` — an odd/AvN parity system
— survives linearization over `ℤ` as a nonzero cohomology class. -/
theorem twistedH1_nonvanishing_frustratedTriangle {a : Fin 3 → Bool}
    (h : Frustrated a) :
    ambCocycle a ∈ LinearMap.ker modD1 ∧
      ambCocycle a ∈ relC1 ∧
      ambCocycle a ∉ Submodule.map (modD0 a) (relC0 a) :=
  ⟨LinearMap.mem_ker.mpr rfl, ambCocycle_mem_relC1 a,
    fun hb => (ambCocycle_mem_relCoboundaries_iff a).mp hb h⟩

/-! ### The computed witness -/

/-- The minimal frustrated instance: one odd edge. -/
def oddTriangle : Fin 3 → Bool := ![true, false, false]

theorem oddTriangle_frustrated : Frustrated oddTriangle := by decide

/-- The odd triangle has no global solutions... -/
theorem oddTriangle_xorTriangle_empty : xorTriangle oddTriangle = ∅ :=
  (xorTriangle_eq_empty_iff oddTriangle).mpr oddTriangle_frustrated

/-- ...and its twisted `Ȟ¹` obstruction class is nonzero: the computed
nonvanishing witness. -/
theorem oddTriangle_nonvanishing :
    ambCocycle oddTriangle ∈ relC1 ∧
      ambCocycle oddTriangle ∉
        Submodule.map (modD0 oddTriangle) (relC0 oddTriangle) :=
  ⟨(twistedH1_nonvanishing_frustratedTriangle oddTriangle_frustrated).2.1,
    (twistedH1_nonvanishing_frustratedTriangle oddTriangle_frustrated).2.2⟩

end STE
