/-
Local (non-tight) gluing: grading the sheaf condition of `Ste.CechCover`
by WHICH subfamily of a cover's contexts admits a glue, not just whether
all of them do.

`Ste.CechCover` asks a single yes/no question of a compatible family: does
it glue over the WHOLE cover (`GluesCover`)?  This file interpolates: a
compatible family may glue over a strict SUBSET of the contexts even when
it fails to glue over all of them.  The collection of subsets a family
glues over (`gluingComplex`) is downward closed (`gluesOn_mono`,
`mem_gluingComplex_of_subset`) -- an abstract simplicial complex on the
context index set `J`, with `CechVanishesCover` exactly the statement that
the top simplex `Set.univ` is present for EVERY compatible family
(`cechVanishesCover_iff_forall_univ_mem_gluingComplex`).  The graded
interpolant `GluesLocallyAt T U k` says every compatible family glues over
every subfamily of size `≤ k`; `GluesCover`/`CechVanishesCover` sit at the
top of the hierarchy (`k = |J|`,
`cechVanishesCover_iff_gluesLocallyAt_card`), and level `1` is UNIVERSAL in
STE for a nonempty context index (`gluesLocallyAt_one`, which carries a
`[Nonempty J]` hypothesis -- it is what supplies the witness in the empty
subfamily case) -- because `localSections` are by definition
extendable to a global witness, "all vertices are present" is free
(`CompatibleFamily.gluesOn_singleton`), the cover-level avatar of the
always-total ambient extension of `Ste.TwistedCech`.

**The witness that level 1 is not level 2.**  The two-variable Boolean
`diagonal` (`Ste.Sheaf`), covered by its own singletons, is 1-locally
gluing (`diagonal_gluesLocallyAt_one`) but not tight
(`diagonal_not_cechVanishesCover`, `Ste.CechCover`), so `2`-local gluing
strictly fails (`diagonal_not_gluesLocallyAt_two`); packaged as
`diagonal_local_not_tight`.  The explicit stuck family `diagMixed` (the
cover-level avatar of `diagonal_mixed_compatible_not_glues`,
`Ste.CechObstruction`) glues over both singleton vertices
(`diagMixed_gluesOn_singleton`) but not over the top edge
(`diagMixed_not_gluesOn_univ`): its gluing complex is exactly the boundary
of the 1-simplex, `∂Δ¹` -- the minimal local-but-not-tight complex
(`diagMixed_gluingComplex`).

**The Helly bridge.**  `GluesOn T U s K` is nonemptiness of the
intersection `T ∩ ⋂ j ∈ K, {f | ...}` of "gluing fibers"
(`gluesOn_iff_nonempty_inter`), so `k`-local gluing IMPLIES `k`-wise
consistency (`Ste.HellyConsistency`'s `KWiseConsistent`) of the family of
fibers (`GluesLocallyAt.kWiseConsistent_gluingFiber`).  Only this
direction is mechanized; the converse is immediate from
`gluesOn_iff_nonempty_inter` but is not stated as a theorem here.  This makes the
local-to-tight gap a HELLY NUMBER: if the fiber family additionally has
Helly number `k` (`HasHelly`), `k`-local gluing upgrades all the way to
tight gluing (`cechVanishesCover_of_hasHelly_gluingFiber`) -- the first
family-level bridge between the Čech modules and `Ste.HellyConsistency`,
echoing the classical Helly theorem for convex sets (E. Helly, 1923) and
the "`k`-consistency implies global consistency" phenomenon of constraint
propagation (`dechter2003constraint`).

**Honest boundary.**  No claim that the gluing complex determines the
Čech obstruction NUMBER (`Ste.CechObstruction`'s `coverCechObstruction`);
no Grothendieck-coverage formalization of the "local" in "local gluing";
no general criterion for which simplicial complexes arise as gluing
complexes; and no witness of level-`k` strictness beyond `k = 2` (e.g. a
parity-constraint family separating higher levels) is mechanized here.

Reference: S. Abramsky, A. Brandenburger, *The sheaf-theoretic structure
of non-locality and contextuality*, New J. Phys. 13 (2011) 113036
(`abramsky2011sheaf`).
-/
import Ste.CechCover
import Ste.HellyConsistency

namespace STE

open Set

variable {V : Type*} {A : V → Type*} {J : Type*}

/-! ### Partial gluing and the gluing complex -/

/-- **Partial gluing over the subfamily `K` of contexts.**  `K = ∅`
degenerates to `T.Nonempty` (`gluesOn_empty_iff`); `K = Set.univ` is
`GluesCover` (`gluesOn_univ_iff`). -/
def GluesOn (T : Set (∀ v, A v)) (U : J → Set V)
    (s : ∀ j, ∀ v : (U j), A v) (K : Set J) : Prop :=
  ∃ f ∈ T, ∀ j ∈ K, (U j).restrict f = s j

/-- **The gluing complex of a family**: all subsets of contexts over which
it glues.  Downward closed (`mem_gluingComplex_of_subset`) -- an abstract
simplicial complex on the context index set `J`. -/
def gluingComplex (T : Set (∀ v, A v)) (U : J → Set V)
    (s : ∀ j, ∀ v : (U j), A v) : Set (Set J) :=
  {K | GluesOn T U s K}

/-- **`k`-partial (local) gluing**: every compatible family glues over
every subfamily of at most `k` contexts. -/
def GluesLocallyAt (T : Set (∀ v, A v)) (U : J → Set V) (k : ℕ) : Prop :=
  ∀ s, CompatibleFamily T U s → ∀ K : Finset J, K.card ≤ k → GluesOn T U s ↑K

/-- **The gluing fiber** of the family at context `j`: the global sections
of `T` restricting to the prescribed section there. -/
def gluingFiber (T : Set (∀ v, A v)) (U : J → Set V)
    (s : ∀ j, ∀ v : (U j), A v) (j : J) : Set (∀ v, A v) :=
  {f ∈ T | (U j).restrict f = s j}

/-! ### Basic facts about `GluesOn` -/

/-- Gluing over a family of contexts glues over any subfamily: the same
global witness works, restricted to a smaller condition. -/
theorem gluesOn_mono {T : Set (∀ v, A v)} {U : J → Set V}
    {s : ∀ j, ∀ v : (U j), A v} {K K' : Set J} (hK : K' ⊆ K)
    (h : GluesOn T U s K) : GluesOn T U s K' := by
  obtain ⟨f, hf, hres⟩ := h
  exact ⟨f, hf, fun j hj => hres j (hK hj)⟩

/-- **`gluingComplex` is downward closed**: it is a genuine abstract
simplicial complex on the context index set. -/
theorem mem_gluingComplex_of_subset {T : Set (∀ v, A v)} {U : J → Set V}
    {s : ∀ j, ∀ v : (U j), A v} {K K' : Set J} (hK : K' ⊆ K)
    (h : K ∈ gluingComplex T U s) : K' ∈ gluingComplex T U s :=
  gluesOn_mono hK h

/-- Gluing over the top simplex is exactly `GluesCover`. -/
theorem gluesOn_univ_iff {T : Set (∀ v, A v)} {U : J → Set V}
    {s : ∀ j, ∀ v : (U j), A v} :
    GluesOn T U s Set.univ ↔ GluesCover T U s := by
  constructor
  · rintro ⟨f, hf, hres⟩
    exact ⟨f, hf, fun j => hres j (Set.mem_univ j)⟩
  · rintro ⟨f, hf, hres⟩
    exact ⟨f, hf, fun j _ => hres j⟩

/-- Gluing over the empty family of contexts is exactly nonemptiness of
`T`: no restriction conditions to satisfy. -/
theorem gluesOn_empty_iff {T : Set (∀ v, A v)} {U : J → Set V}
    {s : ∀ j, ∀ v : (U j), A v} :
    GluesOn T U s ∅ ↔ T.Nonempty := by
  constructor
  · rintro ⟨f, hf, -⟩
    exact ⟨f, hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, hf, fun j hj => ((Set.mem_empty_iff_false j).mp hj).elim⟩

/-- **The STE structural fact "all vertices are present"**: a compatible
family always glues over any single context, because `localSections`
already carries a global witness by definition
(`Ste.VariablePresheaf.mem_localSections`). -/
theorem CompatibleFamily.gluesOn_singleton {T : Set (∀ v, A v)}
    {U : J → Set V} {s : ∀ j, ∀ v : (U j), A v} (hs : CompatibleFamily T U s)
    (j : J) : GluesOn T U s {j} := by
  obtain ⟨g, hg, hgs⟩ := hs.1 j
  refine ⟨g, hg, fun k hk => ?_⟩
  rw [Set.mem_singleton_iff] at hk
  subst hk
  exact hgs

/-! ### The locality hierarchy -/

/-- Demanding gluing at more contexts (larger `k`) is a stronger
hypothesis, so it implies gluing at every smaller level. -/
theorem GluesLocallyAt.mono {T : Set (∀ v, A v)} {U : J → Set V}
    {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) (h : GluesLocallyAt T U k₂) :
    GluesLocallyAt T U k₁ :=
  fun s hs K hK => h s hs K (hK.trans hk)

/-- **Level `1` of the hierarchy is universal in STE.**  Every compatible
family glues over every context subfamily of size `≤ 1`: the empty case
pulls a witness from any single context's compatibility -- note
`CompatibleFamily` itself imposes NO nonemptiness on `J`; the arbitrary
index comes from this theorem's own `[Nonempty J]` instance -- and the
singleton case is `CompatibleFamily.gluesOn_singleton`. -/
theorem gluesLocallyAt_one [Nonempty J] (T : Set (∀ v, A v)) (U : J → Set V) :
    GluesLocallyAt T U 1 := by
  intro s hs K hK
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · subst hKe
    obtain ⟨g, hg, -⟩ := hs.1 (Classical.arbitrary J)
    rw [Finset.coe_empty]
    exact gluesOn_empty_iff.mpr ⟨g, hg⟩
  · have hcard : K.card = 1 := by
      have := hKne.card_pos
      omega
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
    rw [hj, Finset.coe_singleton]
    exact hs.gluesOn_singleton j

/-- Tight gluing (`CechVanishesCover`) implies `k`-local gluing at every
level: the global glue already restricts to any subfamily. -/
theorem CechVanishesCover.gluesLocallyAt {T : Set (∀ v, A v)}
    {U : J → Set V} (h : CechVanishesCover T U) (k : ℕ) :
    GluesLocallyAt T U k := by
  intro s hs K _
  obtain ⟨f, hf, hres⟩ := h s hs
  exact ⟨f, hf, fun j _ => hres j⟩

/-- **Tight = the top of the hierarchy.**  For a finite context set,
`CechVanishesCover` coincides with `GluesLocallyAt` at level `|J|`, where
every subfamily (in particular `Finset.univ`) is admitted. -/
theorem cechVanishesCover_iff_gluesLocallyAt_card [Fintype J]
    {T : Set (∀ v, A v)} {U : J → Set V} :
    CechVanishesCover T U ↔ GluesLocallyAt T U (Fintype.card J) := by
  constructor
  · intro h
    exact h.gluesLocallyAt _
  · intro h s hs
    have hglue := h s hs Finset.univ (le_of_eq Finset.card_univ)
    rw [Finset.coe_univ] at hglue
    exact gluesOn_univ_iff.mp hglue

/-- **Tight gluing = the top simplex is always in the gluing complex.**
Restates `CechVanishesCover` via `gluingComplex` instead of `GluesCover`,
making the "top of the hierarchy" reading explicit. -/
theorem cechVanishesCover_iff_forall_univ_mem_gluingComplex
    {T : Set (∀ v, A v)} {U : J → Set V} :
    CechVanishesCover T U ↔
      ∀ s, CompatibleFamily T U s → Set.univ ∈ gluingComplex T U s := by
  constructor
  · intro h s hs
    exact gluesOn_univ_iff.mpr (h s hs)
  · intro h s hs
    exact gluesOn_univ_iff.mp (h s hs)

/-! ### The Helly bridge -/

/-- **`GluesOn` as nonemptiness of an intersection.**  Gluing over `K` is
exactly the nonemptiness of `T` intersected with the family of
restriction conditions indexed by `K` -- the set-theoretic reading that
feeds `Ste.HellyConsistency`. -/
theorem gluesOn_iff_nonempty_inter {T : Set (∀ v, A v)} {U : J → Set V}
    {s : ∀ j, ∀ v : (U j), A v} {K : Set J} :
    GluesOn T U s K ↔
      (T ∩ ⋂ j ∈ K, {f | (U j).restrict f = s j}).Nonempty := by
  constructor
  · rintro ⟨f, hf, hres⟩
    exact ⟨f, hf, Set.mem_iInter₂.mpr hres⟩
  · rintro ⟨f, hf, hres⟩
    exact ⟨f, hf, Set.mem_iInter₂.mp hres⟩

/-- **`k`-local gluing implies `k`-wise consistency of the gluing
fibers.**
For any subfamily of size `≤ k`, the `GluesOn` witness lies in every
fiber's restriction condition -- exactly `KWiseConsistent`
(`Ste.HellyConsistency`) of the family `gluingFiber T U s`. -/
theorem GluesLocallyAt.kWiseConsistent_gluingFiber {T : Set (∀ v, A v)}
    {U : J → Set V} {k : ℕ} (h : GluesLocallyAt T U k)
    {s : ∀ j, ∀ v : (U j), A v} (hs : CompatibleFamily T U s) :
    KWiseConsistent (gluingFiber T U s) k := by
  intro K hK
  obtain ⟨f, hf, hres⟩ := h s hs K hK
  exact ⟨f, Set.mem_iInter₂.mpr fun j hj => ⟨hf, hres j (Finset.mem_coe.mpr hj)⟩⟩

/-- **The Helly punchline.**  `k`-local gluing upgrades to tight gluing
WHENEVER the gluing-fiber family of every compatible family has Helly
number `k` (sufficiency only; no converse is claimed or mechanized):
`k`-wise consistency (from `GluesLocallyAt`) plus `HasHelly`
gives a point of the fibers' feasibility set, which is precisely a global
glue.  The first family-level bridge between the Čech modules
(`Ste.CechCover`) and `Ste.HellyConsistency`. -/
theorem cechVanishesCover_of_hasHelly_gluingFiber [Nonempty J]
    {T : Set (∀ v, A v)} {U : J → Set V} {k : ℕ}
    (hH : ∀ s, CompatibleFamily T U s → HasHelly (gluingFiber T U s) k)
    (hloc : GluesLocallyAt T U k) : CechVanishesCover T U := by
  intro s hs
  have hkw : KWiseConsistent (gluingFiber T U s) k :=
    hloc.kWiseConsistent_gluingFiber hs
  obtain ⟨f, hf⟩ := hH s hs hkw
  have hmem := mem_feasibilitySet.mp hf
  exact ⟨f, (hmem (Classical.arbitrary J)).1, fun j => (hmem j).2⟩

/-! ### The witness: the diagonal is 1-locally gluing but not tight -/

/-- **Level `1` does not imply level `2`.**  The two-variable Boolean
`diagonal` (`Ste.Sheaf`), covered by its own singletons, is 1-locally
gluing: an instance of the universal fact `gluesLocallyAt_one`. -/
theorem diagonal_gluesLocallyAt_one :
    GluesLocallyAt diagonal (fun v : Fin 2 => ({v} : Set (Fin 2))) 1 :=
  gluesLocallyAt_one diagonal _

/-- The diagonal is NOT `2`-locally gluing for its singleton cover: `2`
is `Fintype.card (Fin 2)`, so `2`-local gluing would be tight gluing
(`cechVanishesCover_iff_gluesLocallyAt_card`), contradicting
`diagonal_not_cechVanishesCover` (`Ste.CechCover`). -/
theorem diagonal_not_gluesLocallyAt_two :
    ¬ GluesLocallyAt diagonal (fun v : Fin 2 => ({v} : Set (Fin 2))) 2 := by
  intro h
  apply diagonal_not_cechVanishesCover
  apply cechVanishesCover_iff_gluesLocallyAt_card.mpr
  rw [Fintype.card_fin]
  exact h

/-- **Headline package**: the diagonal separates level `1` from tight
gluing -- local but not tight. -/
theorem diagonal_local_not_tight :
    GluesLocallyAt diagonal (fun v : Fin 2 => ({v} : Set (Fin 2))) 1 ∧
      ¬ CechVanishesCover diagonal (fun v : Fin 2 => ({v} : Set (Fin 2))) :=
  ⟨diagonal_gluesLocallyAt_one, diagonal_not_cechVanishesCover⟩

/-- **The explicit stuck family, complex form.**  Constant on each
singleton context: the cover-level avatar of
`diagonal_mixed_compatible_not_glues` (`Ste.CechObstruction`). -/
def diagMixed : ∀ j : Fin 2, ∀ _ : ({j} : Set (Fin 2)), Bool :=
  fun j _ => decide (j = 1)

/-- `diagMixed` is a compatible family: each singleton section is the
restriction of the constant global assignment `fun _ => decide (j = 1)`
(a member of `diagonal`), and overlap agreement is forced by the singleton
contexts coinciding, which forces the contexts' indices to coincide. -/
theorem diagMixed_compatibleFamily :
    CompatibleFamily diagonal (fun v : Fin 2 => ({v} : Set (Fin 2))) diagMixed := by
  refine ⟨fun j => ⟨fun _ => decide (j = 1), rfl, rfl⟩, ?_⟩
  intro j k v hv hv'
  have hvj : v = j := Set.mem_singleton_iff.mp hv
  have hvk : v = k := Set.mem_singleton_iff.mp hv'
  subst hvj
  subst hvk
  rfl

/-- `diagMixed` glues over both singleton vertices of the cover: an
instance of the universal structural fact
`CompatibleFamily.gluesOn_singleton`. -/
theorem diagMixed_gluesOn_singleton (j : Fin 2) :
    GluesOn diagonal (fun v : Fin 2 => ({v} : Set (Fin 2))) diagMixed {j} :=
  diagMixed_compatibleFamily.gluesOn_singleton j

/-- `diagMixed` does NOT glue over the top edge: a glue `f` would satisfy
`f 0 = decide (0 = 1) = false` and `f 1 = decide (1 = 1) = true`,
contradicting `f ∈ diagonal` (`f 0 = f 1`). -/
theorem diagMixed_not_gluesOn_univ :
    ¬ GluesOn diagonal (fun v : Fin 2 => ({v} : Set (Fin 2))) diagMixed
      Set.univ := by
  rintro ⟨f, hf, hres⟩
  have h0 : f 0 = decide ((0 : Fin 2) = 1) :=
    congrFun (hres 0 (Set.mem_univ 0)) ⟨0, rfl⟩
  have h1 : f 1 = decide ((1 : Fin 2) = 1) :=
    congrFun (hres 1 (Set.mem_univ 1)) ⟨1, rfl⟩
  have hf01 : f 0 = f 1 := hf
  rw [h0, h1] at hf01
  exact absurd hf01 (by decide)

/-- **The gluing complex of `diagMixed` is `∂Δ¹`**: exactly the proper
subsets of the two-element context set.  Any `K ≠ Set.univ` misses `0` or
`1`, hence sits under a singleton (or is empty), where gluing is free
(`diagMixed_gluesOn_singleton`, `gluesOn_empty_iff`); the converse is
`diagMixed_not_gluesOn_univ`.  The minimal local-but-not-tight gluing
complex. -/
theorem diagMixed_gluingComplex :
    gluingComplex diagonal (fun v : Fin 2 => ({v} : Set (Fin 2))) diagMixed =
      {K | K ≠ Set.univ} := by
  ext K
  simp only [gluingComplex, Set.mem_setOf_eq]
  constructor
  · intro hK hKeq
    exact diagMixed_not_gluesOn_univ (hKeq ▸ hK)
  · intro hK
    by_cases h0 : (0 : Fin 2) ∈ K <;> by_cases h1 : (1 : Fin 2) ∈ K
    · exact absurd (Set.eq_univ_of_forall fun x => by fin_cases x <;> assumption) hK
    · have hsub : K ⊆ ({0} : Set (Fin 2)) := by
        intro x hx
        fin_cases x
        · rfl
        · exact absurd hx h1
      exact gluesOn_mono hsub (diagMixed_gluesOn_singleton 0)
    · have hsub : K ⊆ ({1} : Set (Fin 2)) := by
        intro x hx
        fin_cases x
        · exact absurd hx h0
        · rfl
      exact gluesOn_mono hsub (diagMixed_gluesOn_singleton 1)
    · have hsub : K ⊆ (∅ : Set (Fin 2)) := by
        intro x hx
        fin_cases x
        · exact absurd hx h0
        · exact absurd hx h1
      exact gluesOn_mono hsub (gluesOn_empty_iff.mpr ⟨fun _ => true, rfl⟩)

end STE
