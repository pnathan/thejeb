/-
The variable-side presheaf of local sections.

`Ste.Sheaf` settled the *constraint-side* story: feasibility is a sheaf
for union-covers of the constraint index (`feasibilitySet_eq_iInter_cover`),
rectangular families have product feasible sets
(`rectangular_feasibilitySet`), and the `diagonal` coupling is provably
not rectangular (`diagonal_not_rectangular`).  This file builds the
*variable-side* presheaf and proves the checkable core of the outlook
conjecture "feasibility is a presheaf on subsets of variables, whose
gluing condition holds for tractable fragments and fails at coupling":

* **The presheaf.**  Over a set of variables `W ⊆ V`, the local sections
  `localSections T W` of a constraint `T` are the partial assignments on
  `W` that extend to a global solution of `T` — `T` viewed through the
  coordinates in `W`.  Restriction along `W' ⊆ W` is `Set.restrict₂`.
  Functoriality (`restrict_id`, `restrict_restrict`) and naturality on
  sections (`localSections_restrict₂`) make `W ↦ localSections T W` a
  genuine contravariant functor on the poset of variable subsets.  For a
  constraint supported inside `W` (`Ste.Support`), the sections over `W`
  already decide global membership (`restrict_mem_localSections_iff`).

* **Gluing succeeds in the rectangular case.**  For a rectangular
  constraint `univ.pi P` and the cover of `V` by singletons, the glue of
  the local-section data (`singletonGlue`) recovers the constraint
  exactly (`singletonGlue_pi`, `mem_pi_iff_forall_restrict`), and any
  family of local sections glues to a *unique* global solution
  (`rectangular_glue`).  Overlaps of distinct singletons are empty, so
  pairwise compatibility is automatic and the sheaf condition is exactly
  existence-and-uniqueness of the glue.  A product set is determined by
  its coordinate projections: the presheaf is a sheaf here.

* **Gluing fails at the diagonal.**  The singleton sections of the
  two-bit coupling `diagonal` are full (`localSections_diagonal_singleton`:
  each projection is `univ`, carrying zero information), so its glue is
  all of `Bool × Bool` (`singletonGlue_diagonal`, `encard 4`) — a strict
  overshoot of the true feasible set (`diagonal_ssubset_singletonGlue`,
  `diagonal_encard = 2`).  Concretely there are pairwise-compatible local
  sections, each individually extendable to the diagonal, with *no*
  global diagonal section restricting to them (`diagonal_gluing_fails`):
  the presheaf is not a sheaf for the singleton cover.  The glue of
  singleton sections is always rectangular (`singletonGlue_eq_pi`), so
  failure is forced by `diagonal_not_rectangular`.

The residual conjecture — that variable-side gluing holds *precisely*
for the tractable fragments (the full iff) — is NOT claimed here; it
remains outlook.

References: S. Abramsky, A. Brandenburger, *The sheaf-theoretic structure
of non-locality and contextuality*, 2011 (empirical models as presheaves
over measurement contexts); R. Dechter, *Constraint Processing*, 2003.
-/
import Mathlib.Data.Set.Restrict
import Ste.Support

namespace STE

open Set

variable {V : Type*} {A : V → Type*}

/-! ### The variable-side sections functor -/

/-- **Local sections over a set of variables.**  For a constraint
`T : Set (∀ v, A v)` and variables `W ⊆ V`, the local sections are the
partial assignments on `W` that extend to a global solution of `T`:
the image of `T` under coordinate restriction `Set.restrict`. -/
def localSections (T : Set (∀ v, A v)) (W : Set V) : Set (∀ v : W, A v) :=
  W.restrict '' T

theorem mem_localSections {T : Set (∀ v, A v)} {W : Set V}
    {s : ∀ v : W, A v} :
    s ∈ localSections T W ↔ ∃ f ∈ T, W.restrict f = s :=
  Iff.rfl

/-- Every global solution restricts to a local section: the unit of the
presheaf. -/
theorem restrict_mem_localSections {T : Set (∀ v, A v)} (W : Set V)
    {f : ∀ v, A v} (hf : f ∈ T) : W.restrict f ∈ localSections T W :=
  ⟨f, hf, rfl⟩

/-- **Presheaf identity law.**  Restricting along `W ⊆ W` is the
identity on sections. -/
@[simp] theorem restrict_id (W : Set V) (f : ∀ v : W, A v) :
    Set.restrict₂ Set.Subset.rfl f = f :=
  rfl

/-- **Presheaf composition law.**  Restriction maps compose along
`W'' ⊆ W' ⊆ W`: the sections functor is a genuine contravariant functor
on the poset of variable subsets. -/
theorem restrict_restrict {W W' W'' : Set V} (h₁ : W'' ⊆ W') (h₂ : W' ⊆ W)
    (f : ∀ v : W, A v) :
    Set.restrict₂ h₁ (Set.restrict₂ h₂ f) = Set.restrict₂ (h₁.trans h₂) f :=
  rfl

/-- **Naturality on sections.**  The restriction map carries the local
sections over `W` *onto* the local sections over `W' ⊆ W`: restriction
of an extendable partial assignment is extendable, and every section
over `W'` arises this way. -/
theorem localSections_restrict₂ {W W' : Set V} (h : W' ⊆ W)
    (T : Set (∀ v, A v)) :
    Set.restrict₂ h '' localSections T W = localSections T W' := by
  rw [localSections, localSections, ← Set.image_comp,
    Set.restrict₂_comp_restrict]

/-- **Sections over a support decide membership.**  If `T` is supported
on `σ ⊆ W`, then a global assignment solves `T` iff its restriction to
`W` is a local section: nothing outside the support matters. -/
theorem restrict_mem_localSections_iff {T : Set (∀ v, A v)} {σ W : Set V}
    (hT : HasSupport T σ) (hσW : σ ⊆ W) (f : ∀ v, A v) :
    W.restrict f ∈ localSections T W ↔ f ∈ T := by
  constructor
  · rintro ⟨g, hg, hgf⟩
    exact (hT g f fun v hv => congrFun hgf ⟨v, hσW hv⟩).mp hg
  · exact restrict_mem_localSections W

/-- Restrictions to a singleton agree iff the values at that variable
agree: a section over `{v}` is exactly a value in `A v`. -/
theorem restrict_singleton_eq_iff {f g : ∀ v, A v} {v : V} :
    ({v} : Set V).restrict f = ({v} : Set V).restrict g ↔ f v = g v := by
  constructor
  · intro h
    exact congrFun h ⟨v, rfl⟩
  · intro h
    funext u
    obtain ⟨u, hu⟩ := u
    have hu' : u = v := Set.mem_singleton_iff.mp hu
    subst hu'
    exact h

/-! ### The glue along the singleton cover -/

/-- **The glue of the singleton-cover section data**: all global
assignments whose restriction to each single variable is a local
section.  The sheaf condition for the cover of `V` by singletons asks
`singletonGlue T = T`. -/
def singletonGlue (T : Set (∀ v, A v)) : Set (∀ v, A v) :=
  {f | ∀ v, ({v} : Set V).restrict f ∈ localSections T {v}}

theorem mem_singletonGlue {T : Set (∀ v, A v)} {f : ∀ v, A v} :
    f ∈ singletonGlue T ↔
      ∀ v, ({v} : Set V).restrict f ∈ localSections T {v} :=
  Iff.rfl

/-- Half of the sheaf condition always holds: every constraint is
contained in the glue of its own singleton sections. -/
theorem subset_singletonGlue (T : Set (∀ v, A v)) : T ⊆ singletonGlue T :=
  fun _ hf => mem_singletonGlue.mpr fun _ => restrict_mem_localSections _ hf

/-- **The glue is always rectangular**: gluing the singleton sections of
any constraint yields the product of its coordinate projections — the
tightest rectangle containing it that the local data can see. -/
theorem singletonGlue_eq_pi (T : Set (∀ v, A v)) :
    singletonGlue T = Set.univ.pi fun v => (fun f => f v) '' T := by
  ext f
  simp only [mem_singletonGlue, Set.mem_univ_pi, mem_localSections,
    Set.mem_image]
  refine forall_congr' fun v => ?_
  constructor
  · rintro ⟨g, hg, hgf⟩
    exact ⟨g, hg, restrict_singleton_eq_iff.mp hgf⟩
  · rintro ⟨g, hg, hgv⟩
    exact ⟨g, hg, restrict_singleton_eq_iff.mpr hgv⟩

/-! ### Gluing succeeds for rectangular constraints (the sheaf case) -/

/-- **Sheaf condition, rectangular case.**  For a rectangular constraint
the glue of the singleton sections recovers the constraint exactly: a
product set is determined by its coordinate projections. -/
theorem singletonGlue_pi (P : ∀ v, Set (A v)) :
    singletonGlue (Set.univ.pi P) = Set.univ.pi P := by
  refine Set.Subset.antisymm ?_ (subset_singletonGlue _)
  intro f hf
  rw [Set.mem_univ_pi]
  intro v
  obtain ⟨g, hg, hgf⟩ := mem_localSections.mp (mem_singletonGlue.mp hf v)
  have hgv : g v = f v := congrFun hgf ⟨v, rfl⟩
  exact hgv ▸ Set.mem_univ_pi.mp hg v

/-- **Local-to-global for rectangular constraints**: membership in a
product constraint is decided by the singleton sections alone. -/
theorem mem_pi_iff_forall_restrict (P : ∀ v, Set (A v)) (f : ∀ v, A v) :
    f ∈ Set.univ.pi P ↔
      ∀ v, ({v} : Set V).restrict f ∈ localSections (Set.univ.pi P) {v} := by
  rw [← mem_singletonGlue, singletonGlue_pi]

/-- **Gluing succeeds for rectangular constraints.**  Any family of
local sections of a rectangular constraint over the singleton cover
(distinct singletons have empty overlap, so pairwise compatibility is
automatic) glues to a *unique* global solution.  This is the sheaf
existence-and-uniqueness condition, satisfied in the tractable case. -/
theorem rectangular_glue (P : ∀ v, Set (A v))
    (s : ∀ v : V, ∀ u : ({v} : Set V), A u)
    (hs : ∀ v, s v ∈ localSections (Set.univ.pi P) {v}) :
    ∃! f : ∀ v, A v, f ∈ Set.univ.pi P ∧
      ∀ v, ({v} : Set V).restrict f = s v := by
  refine ⟨fun v => s v ⟨v, rfl⟩, ⟨?_, ?_⟩, ?_⟩
  · -- the pointwise glue solves the rectangular constraint
    rw [Set.mem_univ_pi]
    intro v
    obtain ⟨g, hg, hgs⟩ := mem_localSections.mp (hs v)
    have hgv : g v = s v ⟨v, rfl⟩ := congrFun hgs ⟨v, rfl⟩
    exact hgv ▸ Set.mem_univ_pi.mp hg v
  · -- it restricts to the prescribed local sections
    intro v
    funext u
    obtain ⟨u, hu⟩ := u
    have hu' : u = v := Set.mem_singleton_iff.mp hu
    subst hu'
    rfl
  · -- and it is the only global assignment doing so
    rintro f' ⟨-, hres⟩
    funext v
    exact congrFun (hres v) ⟨v, rfl⟩

/-! ### Gluing fails at the diagonal (the obstruction) -/

/-- **The singleton sections of the coupling are full**: every partial
assignment on one variable extends to the diagonal (choose the constant
assignment).  Each projection of `diagonal` is all of `Bool` — the local
data carries zero information about the coupling. -/
theorem localSections_diagonal_singleton (v : Fin 2) :
    localSections diagonal ({v} : Set (Fin 2)) = Set.univ := by
  refine Set.eq_univ_of_forall fun s =>
    mem_localSections.mpr ⟨fun _ => s ⟨v, rfl⟩, rfl, ?_⟩
  funext u
  obtain ⟨u, hu⟩ := u
  have hu' : u = v := Set.mem_singleton_iff.mp hu
  subst hu'
  rfl

/-- The glue of the diagonal's singleton sections is the whole two-bit
space: the local data reconstructs all four assignments, not the two
diagonal ones. -/
theorem singletonGlue_diagonal : singletonGlue diagonal = Set.univ := by
  refine Set.eq_univ_of_forall fun f => mem_singletonGlue.mpr fun v => ?_
  rw [localSections_diagonal_singleton]
  exact Set.mem_univ _

/-- The diagonal is not recovered by gluing its singleton sections:
the glue is rectangular (`singletonGlue_eq_pi`), and the diagonal is
not (`diagonal_not_rectangular`). -/
theorem diagonal_ne_singletonGlue : diagonal ≠ singletonGlue diagonal :=
  fun h => diagonal_not_rectangular
    ⟨fun v => (fun f => f v) '' diagonal, h.trans (singletonGlue_eq_pi diagonal)⟩

/-- **Sheaf condition fails at the coupling**: the diagonal is a
*strict* subset of the glue of its own singleton sections.  Compare
`singletonGlue_pi`, where equality holds. -/
theorem diagonal_ssubset_singletonGlue :
    diagonal ⊂ singletonGlue diagonal :=
  Set.ssubset_iff_subset_ne.mpr
    ⟨subset_singletonGlue diagonal, diagonal_ne_singletonGlue⟩

/-- **The quantitative gap, presheaf form**: the glue of the diagonal's
singleton sections has four points while the diagonal has two
(`diagonal_encard`) — gluing the local data doubles the feasible set. -/
theorem singletonGlue_diagonal_encard :
    (singletonGlue diagonal).encard = 4 := by
  rw [singletonGlue_diagonal, encard_univ_two_bits]

/-- **Gluing fails for the diagonal.**  There is a family of local
sections over the singleton cover of `Fin 2` — pairwise compatible since
distinct singletons do not overlap, and each individually extendable to
the diagonal (`localSections_diagonal_singleton`) — that is restricted
to by *no* global diagonal section: assign `false` at variable `0` and
`true` at variable `1`.  The variable-side presheaf of the coupling
constraint is not a sheaf for the singleton cover. -/
theorem diagonal_gluing_fails :
    ∃ s : ∀ v : Fin 2, ∀ u : ({v} : Set (Fin 2)), Bool,
      (∀ v, s v ∈ localSections diagonal {v}) ∧
      ¬ ∃ f : Fin 2 → Bool, f ∈ diagonal ∧
          ∀ v, ({v} : Set (Fin 2)).restrict f = s v := by
  refine ⟨fun v _ => decide (v = 1), fun v => ?_, ?_⟩
  · rw [localSections_diagonal_singleton]
    exact Set.mem_univ _
  · rintro ⟨f, hf, hres⟩
    have h0 : f 0 = decide ((0 : Fin 2) = 1) := congrFun (hres 0) ⟨0, rfl⟩
    have h1 : f 1 = decide ((1 : Fin 2) = 1) := congrFun (hres 1) ⟨1, rfl⟩
    have hf' : f 0 = f 1 := hf
    rw [h0, h1] at hf'
    exact absurd hf' (by decide)

end STE
