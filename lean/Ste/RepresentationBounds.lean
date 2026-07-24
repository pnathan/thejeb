/-
Representation bounds: rectangle-cover complexity versus the Čech
obstruction — the open item "obstruction size = representation blow-up"
settled as a SANDWICH OF BOUNDS, with the equality reading REFUTED.

The open question asked whether the Čech obstruction number of
`Ste.CechObstruction` EQUALS the "forced representation blow-up" of the
constraint.  There are two readings of "blow-up", and they part ways:

**Reading 1 — the box gap (equality holds, tautologically).**  The
smallest rectangle containing `T` is the box `∏ᵥ projᵥ(T)`, which is
exactly `compatibleFamilies T`.  The obstruction IS the box gap by
unfolding: `cechObstruction T = |compatibleFamilies T| − |T|`
(`cechObstruction_eq_box_sub_encard`, with
`compatibleFamilies_eq_boxProduct` making the box explicit).  This
equality is definitional bookkeeping, not a theorem about
representations.

**Reading 2 — rectangle-cover complexity (the real one; equality
FAILS).**  Following the cover number `C¹` of nondeterministic
communication complexity (Kushilevitz–Nisan 1997; Yannakakis 1991 for
the LP/extension-complexity side), define `rectCoverNumber T` = the
least number of rectangles (product sets) whose union is exactly `T` —
the size of the smallest exact "union of boxes" representation of the
constraint.  What is TRUE is the sandwich, all machine-checked below:

* `foolingNumber_le_rectCoverNumber` : every fooling set `F ⊆ T` (no
  sub-rectangle of `T` contains two distinct points of `F`) has
  `|F| ≤ ρ(T)` — each cover rectangle holds at most one fooling point
  (`IsFoolingSet.encard_le_of_hasRectCover`).
* `rectCoverNumber_le_encard` : `ρ(T) ≤ |T|` — singletons are
  rectangles (`isRectangle_singleton`), so `T` covers itself pointwise.
* `rectCoverNumber_eq_one_iff` / `rectCoverNumber_eq_one_iff_cechVanishes` /
  `one_lt_rectCoverNumber_iff` : for nonempty `T`,
  `ρ(T) = 1 ⟺ T is a rectangle ⟺ the Čech obstruction vanishes`, and
  `ρ(T) ≥ 2 ⟺ the obstruction is nonvanishing` — at the BOTTOM of the
  scale the two invariants agree exactly (via
  `cechVanishes_iff_rectangular`, `Ste.CouplingLowerBound`).
* `rectCoverNumber_allEqual` : the coupling `allEqual n α` (`n ≥ 2`,
  `k = |α|`) has `ρ = k` exactly — the `k` constant vectors are a
  fooling set (`isFoolingSet_allEqual`), giving `k ≤ ρ`, and `ρ ≤ |T| = k`
  closes the sandwich.  Also `foolingNumber_allEqual : foolingNumber = k`.

**The refutation of the equality (Reading 2).**  The raw obstruction
magnitude and `ρ` admit NO uniform inequality in either direction:

* a nonempty rectangle has obstruction `0 < 1 = ρ`
  (`exists_cechObstruction_lt_rectCoverNumber`, witness `univ` on one
  Boolean variable) — so no uniform `ρ ≤ obstruction`;
* the coupling `allEqual n α` with `n ≥ 3`, `k ≥ 2` has
  `ρ = k < kⁿ − k = obstruction`
  (`rectCoverNumber_lt_cechObstruction_allEqual`,
  `exists_rectCoverNumber_lt_cechObstruction`, witness `allEqual 3 Bool`:
  `ρ = 2 < 6`) — so no uniform `obstruction ≤ ρ`.

Both failures are packaged as
`not_forall_rectCoverNumber_le_cechObstruction` and
`not_forall_cechObstruction_le_rectCoverNumber`.  The presumed origin of
the conjecture is also identified: at the MINIMAL nonvanishing instance,
the two-variable Boolean `diagonal`, the equality DOES hold —
`diagonal = allEqual 2 Bool` (`diagonal_eq_allEqual`),
`ρ(diagonal) = 2 = cechObstruction diagonal`
(`rectCoverNumber_diagonal`, `diagonal_cechObstruction_eq_rectCoverNumber`)
— and it fails already at `n = 3` (`2 < 6`).  The equality is a
coincidence of the smallest example, not a law.

**Honest boundary.**  Mechanized here: the definitions `IsRectangle`,
`HasRectCover`, `rectCoverNumber`, `IsFoolingSet`, `foolingNumber`; the
fooling-set lower bound; the `|T|` upper bound; the `ρ = 1` ⟺ vanishing
characterization; the exact value `ρ(allEqual n α) = |α|`; and the two
strict-separation witnesses.  NOT mechanized (outlook): the log-relation
`log ρ ≤ nondeterministic communication complexity ≤ log ρ + O(log |T|)`
of Kushilevitz–Nisan; nonnegative-rank / extension-complexity refinements
(Yannakakis 1991, Fiorini et al. 2015); and cover numbers for covers with
nonempty overlaps (`Ste.CechCover`).

References: E. Kushilevitz, N. Nisan, *Communication Complexity*, CUP
1997 (`kushilevitz1997communication`); M. Yannakakis, *Expressing
combinatorial optimization problems by linear programs*, JCSS 43 (1991)
(`yannakakis1991expressing`); A. Aho, J. Ullman, M. Yannakakis, STOC 1983
(`aho1983notions`; origin of rectangle covers and fooling sets);
S. Abramsky, A. Brandenburger, New J. Phys. 13 (2011)
(`abramsky2011sheaf`).
-/
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Ste.CouplingLowerBound

namespace STE

open Set

variable {V : Type*} {A : V → Type*}

/-! ### Rectangles and rectangle covers -/

/-- A *rectangle* (product set, variable-separable constraint): a set of
assignments of the form `∏ᵥ Pᵥ`.  Rectangles are exactly the constraints
with vanishing Čech obstruction (`cechVanishes_iff_rectangular`). -/
def IsRectangle (R : Set (∀ v, A v)) : Prop :=
  ∃ P : ∀ v, Set (A v), R = Set.univ.pi P

/-- The whole space is a rectangle. -/
theorem isRectangle_univ : IsRectangle (Set.univ : Set (∀ v, A v)) :=
  ⟨fun _ => Set.univ, (Set.pi_univ Set.univ).symm⟩

/-- Every singleton is a rectangle: `{f} = ∏ᵥ {f v}`.  This is the
degenerate representation that makes `ρ(T) ≤ |T|` possible. -/
theorem isRectangle_singleton (f : ∀ v, A v) :
    IsRectangle ({f} : Set (∀ v, A v)) := by
  refine ⟨fun v => {f v}, ?_⟩
  ext g
  constructor
  · rintro rfl
    exact Set.mem_univ_pi.mpr fun v => rfl
  · intro hg
    exact Set.mem_singleton_iff.mpr
      (funext fun v => Set.mem_singleton_iff.mp (Set.mem_univ_pi.mp hg v))

/-- Rectangles are closed under coordinatewise mixing: if `f, g ∈ R` and
`R` is a rectangle, then the hybrid taking `f`'s value where `p` holds
and `g`'s elsewhere is again in `R`.  This is the engine of every
fooling-set argument. -/
theorem IsRectangle.mix_mem {R : Set (∀ v, A v)} (hR : IsRectangle R)
    {f g : ∀ v, A v} (hf : f ∈ R) (hg : g ∈ R) (p : V → Prop)
    [DecidablePred p] : (fun v => if p v then f v else g v) ∈ R := by
  obtain ⟨P, rfl⟩ := hR
  refine Set.mem_univ_pi.mpr fun v => ?_
  by_cases hv : p v
  · rw [if_pos hv]
    exact Set.mem_univ_pi.mp hf v
  · rw [if_neg hv]
    exact Set.mem_univ_pi.mp hg v

/-- `T` admits an exact cover by `m` rectangles: `T = R₀ ∪ ⋯ ∪ R_{m−1}`
with each `Rᵢ` a rectangle.  Since the union is exactly `T`, each `Rᵢ`
is automatically a sub-rectangle of `T`. -/
def HasRectCover (T : Set (∀ v, A v)) (m : ℕ) : Prop :=
  ∃ R : Fin m → Set (∀ v, A v), (∀ i, IsRectangle (R i)) ∧ ⋃ i, R i = T

/-- The empty cover covers exactly the empty constraint. -/
theorem hasRectCover_zero_iff {T : Set (∀ v, A v)} :
    HasRectCover T 0 ↔ T = ∅ := by
  constructor
  · rintro ⟨R, -, hunion⟩
    rw [← hunion]
    exact Set.iUnion_of_empty R
  · rintro rfl
    exact ⟨fun i => i.elim0, fun i => i.elim0, Set.iUnion_of_empty _⟩

/-- **Rectangle-cover complexity** `ρ(T)`: the least number of
rectangles whose union is exactly `T` (`⊤` if no finite cover exists).
This is the exact analogue of the cover number `C¹` of nondeterministic
communication complexity (Kushilevitz–Nisan 1997), read on the constraint
`T` as a `|V|`-dimensional 0/1 tensor: the size of the smallest faithful
"union of boxes" representation of `T`. -/
noncomputable def rectCoverNumber (T : Set (∀ v, A v)) : ℕ∞ :=
  sInf ((fun m : ℕ => (m : ℕ∞)) '' {m : ℕ | HasRectCover T m})

/-- Any explicit cover bounds the cover number. -/
theorem rectCoverNumber_le {T : Set (∀ v, A v)} {m : ℕ}
    (h : HasRectCover T m) : rectCoverNumber T ≤ m :=
  sInf_le ⟨m, h, rfl⟩

/-- A lower bound valid for every cover size is a lower bound on the
cover number. -/
theorem le_rectCoverNumber {T : Set (∀ v, A v)} {k : ℕ∞}
    (h : ∀ m : ℕ, HasRectCover T m → k ≤ m) : k ≤ rectCoverNumber T :=
  le_sInf (by rintro b ⟨m, hm, rfl⟩; exact h m hm)

/-- If any finite cover exists, the cover number is attained by an
actual minimal cover (`ℕ` is well-ordered). -/
theorem exists_rectCoverNumber_eq {T : Set (∀ v, A v)}
    (h : ∃ m, HasRectCover T m) :
    ∃ m : ℕ, rectCoverNumber T = m ∧ HasRectCover T m := by
  have hne : {m : ℕ | HasRectCover T m}.Nonempty := h
  refine ⟨sInf {m : ℕ | HasRectCover T m}, ?_, Nat.sInf_mem hne⟩
  apply le_antisymm
  · exact rectCoverNumber_le (Nat.sInf_mem hne)
  · exact le_rectCoverNumber fun m hm =>
      ENat.coe_le_coe.mpr (Nat.sInf_le hm)

/-- A finite cover number means some finite cover exists. -/
theorem exists_hasRectCover_of_ne_top {T : Set (∀ v, A v)}
    (h : rectCoverNumber T ≠ ⊤) : ∃ m, HasRectCover T m := by
  by_contra hc
  apply h
  have hempty : {m : ℕ | HasRectCover T m} = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun m hm => hc ⟨m, hm⟩
  rw [rectCoverNumber, hempty, Set.image_empty, sInf_empty]

/-- `ρ(T) = 0` exactly for the empty constraint. -/
theorem rectCoverNumber_eq_zero_iff {T : Set (∀ v, A v)} :
    rectCoverNumber T = 0 ↔ T = ∅ := by
  constructor
  · intro h
    obtain ⟨m, hval, hcov⟩ :=
      exists_rectCoverNumber_eq (exists_hasRectCover_of_ne_top
        (by rw [h]; exact ENat.zero_ne_top))
    have hm : m = 0 := by
      have : ((m : ℕ) : ℕ∞) = 0 := hval.symm.trans h
      exact_mod_cast this
    exact hasRectCover_zero_iff.mp (hm ▸ hcov)
  · rintro rfl
    exact le_antisymm
      (by exact_mod_cast rectCoverNumber_le (hasRectCover_zero_iff.mpr rfl))
      zero_le

/-- A nonempty constraint needs at least one rectangle. -/
theorem one_le_rectCoverNumber {T : Set (∀ v, A v)} (hT : T.Nonempty) :
    1 ≤ rectCoverNumber T :=
  le_rectCoverNumber fun m hm => by
    match m with
    | 0 =>
      rw [hasRectCover_zero_iff] at hm
      exact absurd (hm ▸ hT) Set.not_nonempty_empty
    | m + 1 =>
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)

/-! ### The upper bound `ρ(T) ≤ |T|` -/

/-- **The trivial upper bound**: `ρ(T) ≤ |T|` — every constraint is the
union of its singletons, and singletons are rectangles.  (For infinite
`T` the right side is `⊤` and the bound is vacuous.) -/
theorem rectCoverNumber_le_encard (T : Set (∀ v, A v)) :
    rectCoverNumber T ≤ T.encard := by
  by_cases hfin : T.Finite
  · classical
    have hcov : HasRectCover T hfin.toFinset.card := by
      refine ⟨fun i => {(hfin.toFinset.equivFin.symm i : ∀ v, A v)},
        fun i => isRectangle_singleton _, ?_⟩
      ext x
      simp only [Set.mem_iUnion, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        exact hfin.mem_toFinset.mp (hfin.toFinset.equivFin.symm i).2
      · intro hx
        exact ⟨hfin.toFinset.equivFin ⟨x, hfin.mem_toFinset.mpr hx⟩,
          by simp⟩
    calc rectCoverNumber T ≤ (hfin.toFinset.card : ℕ∞) :=
          rectCoverNumber_le hcov
      _ = T.encard := (hfin.encard_eq_coe_toFinset_card).symm
  · rw [Set.Infinite.encard_eq hfin]
    exact le_top

/-! ### Fooling sets and the lower bound -/

/-- A **fooling set** for `T`: a subset `F ⊆ T` such that no
sub-rectangle of `T` contains two distinct points of `F`.  This is the
abstract form of the fooling-set method of communication complexity
(Kushilevitz–Nisan 1997, §1.3): any exact rectangle cover of `T` must
spend a separate rectangle on each point of `F`. -/
def IsFoolingSet (T F : Set (∀ v, A v)) : Prop :=
  F ⊆ T ∧ ∀ R : Set (∀ v, A v), IsRectangle R → R ⊆ T →
    ∀ f ∈ F, ∀ g ∈ F, f ∈ R → g ∈ R → f = g

/-- **Fooling number**: the largest cardinality of a fooling set for
`T`. -/
noncomputable def foolingNumber (T : Set (∀ v, A v)) : ℕ∞ :=
  ⨆ F ∈ {F : Set (∀ v, A v) | IsFoolingSet T F}, F.encard

/-- Every fooling set witnesses a lower bound for `foolingNumber`. -/
theorem IsFoolingSet.le_foolingNumber {T F : Set (∀ v, A v)}
    (hF : IsFoolingSet T F) : F.encard ≤ foolingNumber T :=
  le_iSup₂ (f := fun F _ => F.encard) F hF

/-- **The fooling-set bound, pointwise**: an exact cover of `T` by `m`
rectangles allocates at most one fooling point per rectangle, so
`|F| ≤ m`.  Each cover rectangle is a sub-rectangle of `T` (the union is
exactly `T`), so the fooling property applies to it directly. -/
theorem IsFoolingSet.encard_le_of_hasRectCover {T F : Set (∀ v, A v)}
    (hF : IsFoolingSet T F) {m : ℕ} (hm : HasRectCover T m) :
    F.encard ≤ (m : ℕ∞) := by
  classical
  obtain ⟨R, hrect, hunion⟩ := hm
  match m with
  | 0 =>
    have hT : T = ∅ := hasRectCover_zero_iff.mp ⟨R, hrect, hunion⟩
    have hFe : F = ∅ := Set.subset_empty_iff.mp (hT ▸ hF.1)
    simp [hFe]
  | m + 1 =>
    have hsub : ∀ i, R i ⊆ T := fun i => by
      rw [← hunion]; exact Set.subset_iUnion R i
    have hmem : ∀ f ∈ F, ∃ i, f ∈ R i := fun f hf => by
      have hfT : f ∈ ⋃ i, R i := by rw [hunion]; exact hF.1 hf
      exact Set.mem_iUnion.mp hfT
    set idx : (∀ v, A v) → Fin (m + 1) := fun f =>
      if h : ∃ i, f ∈ R i then h.choose else 0 with hidxdef
    have hidx : ∀ f ∈ F, f ∈ R (idx f) := fun f hf => by
      have h := hmem f hf
      simp only [hidxdef, dif_pos h]
      exact h.choose_spec
    have hinj : Set.InjOn idx F := fun f hf g hg hfg =>
      hF.2 (R (idx f)) (hrect _) (hsub _) f hf g hg (hidx f hf)
        (by rw [hfg]; exact hidx g hg)
    calc F.encard = (idx '' F).encard := (hinj.encard_image).symm
      _ ≤ (Set.univ : Set (Fin (m + 1))).encard :=
          Set.encard_mono (Set.subset_univ _)
      _ = ((m + 1 : ℕ) : ℕ∞) := by
          rw [Set.encard_univ, ENat.card_eq_coe_fintype_card,
            Fintype.card_fin]

/-- **The fooling-set lower bound**: `foolingNumber T ≤ ρ(T)`.  Together
with `rectCoverNumber_le_encard` this is the sandwich
`foolingNumber T ≤ ρ(T) ≤ |T|`. -/
theorem foolingNumber_le_rectCoverNumber (T : Set (∀ v, A v)) :
    foolingNumber T ≤ rectCoverNumber T :=
  iSup₂_le fun _ hF =>
    le_rectCoverNumber fun _ hm => hF.encard_le_of_hasRectCover hm

/-! ### `ρ = 1` is exactly vanishing obstruction -/

/-- **The bottom of the scale**: `ρ(T) = 1` iff `T` is a nonempty
rectangle. -/
theorem rectCoverNumber_eq_one_iff {T : Set (∀ v, A v)} :
    rectCoverNumber T = 1 ↔ T.Nonempty ∧ IsRectangle T := by
  constructor
  · intro h
    obtain ⟨m, hval, hcov⟩ := exists_rectCoverNumber_eq
      (exists_hasRectCover_of_ne_top (by rw [h]; exact ENat.one_ne_top))
    have hm : m = 1 := by
      have : ((m : ℕ) : ℕ∞) = 1 := hval.symm.trans h
      exact_mod_cast this
    subst hm
    obtain ⟨R, hrect, hunion⟩ := hcov
    have hTR : T = R 0 := by
      rw [← hunion]
      ext x
      simp only [Set.mem_iUnion]
      exact ⟨fun ⟨i, hi⟩ => by rwa [Fin.eq_zero i] at hi,
        fun hx => ⟨0, hx⟩⟩
    have hne : T.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      rintro rfl
      exact zero_ne_one
        ((rectCoverNumber_eq_zero_iff.mpr rfl).symm.trans h)
    exact ⟨hne, by rw [hTR]; exact hrect 0⟩
  · rintro ⟨hne, hrectT⟩
    apply le_antisymm
    · have hcov : HasRectCover T 1 :=
        ⟨fun _ => T, fun _ => hrectT, Set.iUnion_const T⟩
      exact_mod_cast rectCoverNumber_le hcov
    · exact one_le_rectCoverNumber hne

/-- **The bridge to the Čech obstruction**: for nonempty `T`,
`ρ(T) = 1` iff the Čech obstruction of the singleton cover vanishes
(via `cechVanishes_iff_rectangular`, `Ste.CouplingLowerBound`). -/
theorem rectCoverNumber_eq_one_iff_cechVanishes {T : Set (∀ v, A v)}
    (hT : T.Nonempty) : rectCoverNumber T = 1 ↔ CechVanishes T := by
  constructor
  · intro h
    exact (cechVanishes_iff_rectangular T).mpr
      (rectCoverNumber_eq_one_iff.mp h).2
  · intro h
    exact rectCoverNumber_eq_one_iff.mpr
      ⟨hT, (cechVanishes_iff_rectangular T).mp h⟩

/-- **Nonvanishing obstruction is exactly `ρ ≥ 2`**: for nonempty `T`,
the Čech obstruction fails to vanish iff `T` needs at least two
rectangles. -/
theorem one_lt_rectCoverNumber_iff {T : Set (∀ v, A v)}
    (hT : T.Nonempty) : 1 < rectCoverNumber T ↔ ¬CechVanishes T := by
  rw [← rectCoverNumber_eq_one_iff_cechVanishes hT]
  constructor
  · exact fun h h1 => h.ne' h1
  · exact fun h =>
      lt_of_le_of_ne (one_le_rectCoverNumber hT) (Ne.symm h)

/-! ### Reading 1: the box gap — where the equality DOES hold -/

/-- The box of `T` — the smallest rectangle containing `T`, the product
of the per-variable projections — is literally `compatibleFamilies T`
(`Ste.CechObstruction`): the two notions coincide by definition. -/
theorem compatibleFamilies_eq_boxProduct (T : Set (∀ v, A v)) :
    compatibleFamilies T = Set.univ.pi fun v => (fun f => f v) '' T :=
  rfl

/-- **The box-gap equality (Reading 1, tautological)**: the Čech
obstruction IS the box gap `|box(T)| − |T|`.  This is the only reading
under which "obstruction = representation blow-up" is an equality — and
it holds by unfolding definitions, not by a representation theorem. -/
theorem cechObstruction_eq_box_sub_encard (T : Set (∀ v, A v)) :
    cechObstruction T = (compatibleFamilies T).encard - T.encard := by
  unfold cechObstruction
  rw [gluedFamilies_eq]

/-! ### The coupling: `ρ(allEqual n α) = |α|` exactly -/

/-- **The constant vectors fool every sub-rectangle**: for `n ≥ 2` the
all-equal constraint is a fooling set for itself.  If a sub-rectangle of
`allEqual` contained two distinct constant vectors, mixing them
(`IsRectangle.mix_mem`) would produce a non-constant hybrid inside
`allEqual` — contradiction. -/
theorem isFoolingSet_allEqual {n : ℕ} {α : Type*} (hn : 2 ≤ n) :
    IsFoolingSet (allEqual n α) (allEqual n α) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  refine ⟨subset_rfl, ?_⟩
  rintro R hR hRT f hf g hg hfR hgR
  classical
  have hmix : (fun j : Fin (m + 2) => if j = 0 then f j else g j) ∈ R :=
    hR.mix_mem hfR hgR fun j => j = 0
  have hall : (fun j : Fin (m + 2) => if j = 0 then f j else g j)
      ∈ allEqual (m + 2) α := hRT hmix
  have hne : (1 : Fin (m + 2)) ≠ 0 := Fin.ne_of_val_ne (by simp)
  have h01 : (if (0 : Fin (m + 2)) = 0 then f 0 else g 0)
      = (if (1 : Fin (m + 2)) = 0 then f 1 else g 1) := hall 0 1
  rw [if_pos rfl, if_neg hne] at h01
  -- h01 : f 0 = g 1
  funext j
  calc f j = f 0 := hf j 0
    _ = g 1 := h01
    _ = g j := hg 1 j

/-- **The coupling, exactly**: `ρ(allEqual n α) = |α|` for `n ≥ 2`.
The sandwich closes: the `|α|` constant vectors are a fooling set
(lower bound), and `allEqual` has only `|α|` points (upper bound).
Contrast `cechObstruction_allEqual`: the obstruction is `|α|ⁿ − |α|` —
exponentially larger for `n ≥ 3`. -/
theorem rectCoverNumber_allEqual {n : ℕ} {α : Type*} [Fintype α]
    (hn : 2 ≤ n) :
    rectCoverNumber (allEqual n α) = (Fintype.card α : ℕ∞) := by
  have hn1 : 1 ≤ n := le_trans one_le_two hn
  apply le_antisymm
  · calc rectCoverNumber (allEqual n α) ≤ (allEqual n α).encard :=
        rectCoverNumber_le_encard _
      _ = (Fintype.card α : ℕ∞) := allEqual_encard hn1
  · calc (Fintype.card α : ℕ∞) = (allEqual n α).encard :=
        (allEqual_encard hn1).symm
      _ ≤ rectCoverNumber (allEqual n α) :=
        le_rectCoverNumber fun _ hm =>
          (isFoolingSet_allEqual hn).encard_le_of_hasRectCover hm

/-- The fooling number of the coupling is also exactly `|α|`: the
sandwich `|α| ≤ foolingNumber ≤ ρ = |α|` pinches. -/
theorem foolingNumber_allEqual {n : ℕ} {α : Type*} [Fintype α]
    (hn : 2 ≤ n) :
    foolingNumber (allEqual n α) = (Fintype.card α : ℕ∞) :=
  le_antisymm
    ((foolingNumber_le_rectCoverNumber _).trans_eq
      (rectCoverNumber_allEqual hn))
    ((allEqual_encard (le_trans one_le_two hn)).symm.trans_le
      (isFoolingSet_allEqual hn).le_foolingNumber)

/-! ### Reading 2 refuted: no uniform inequality in either direction -/

/-- **Strict separation, coupling side**: for `n ≥ 3` and `|α| ≥ 2`,
`ρ(allEqual n α) = |α| < |α|ⁿ − |α| = cechObstruction (allEqual n α)`.
The obstruction strictly exceeds the true representation size — so no
uniform `obstruction ≤ ρ`. -/
theorem rectCoverNumber_lt_cechObstruction_allEqual {n : ℕ} {α : Type*}
    [Fintype α] (hn : 3 ≤ n) (hα : 2 ≤ Fintype.card α) :
    rectCoverNumber (allEqual n α) < cechObstruction (allEqual n α) := by
  have hn2 : 2 ≤ n := le_trans (by norm_num) hn
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  rw [rectCoverNumber_allEqual hn2, cechObstruction_allEqual hn1,
    ENat.coe_lt_coe]
  set k := Fintype.card α with hk
  have h2k : 2 * k < k ^ n := by
    calc 2 * k < 2 * 2 * k := by omega
      _ ≤ k * k * k := Nat.mul_le_mul (Nat.mul_le_mul hα hα) le_rfl
      _ = k ^ 3 := by ring
      _ ≤ k ^ n := Nat.pow_le_pow_right (by omega) hn
  generalize k ^ n = K at h2k ⊢
  omega

/-- **Witness, coupling side**: `allEqual 3 Bool` has `ρ = 2` but
obstruction `2³ − 2 = 6`. -/
theorem exists_rectCoverNumber_lt_cechObstruction :
    ∃ (V : Type) (A : V → Type) (T : Set (∀ v, A v)),
      rectCoverNumber T < cechObstruction T :=
  ⟨Fin 3, fun _ => Bool, allEqual 3 Bool,
    rectCoverNumber_lt_cechObstruction_allEqual le_rfl
      Fintype.card_bool.ge⟩

/-- **Witness, rectangle side**: the full rectangle `univ` on one
Boolean variable has vanishing obstruction but `ρ = 1` — the obstruction
strictly undershoots the representation size, so no uniform
`ρ ≤ obstruction`. -/
theorem exists_cechObstruction_lt_rectCoverNumber :
    ∃ (V : Type) (A : V → Type) (T : Set (∀ v, A v)),
      cechObstruction T < rectCoverNumber T := by
  refine ⟨Fin 1, fun _ => Bool, Set.univ, ?_⟩
  have h0 : cechObstruction (Set.univ : Set (∀ _ : Fin 1, Bool)) = 0 := by
    obtain ⟨P, hP⟩ :=
      (isRectangle_univ : IsRectangle (Set.univ : Set (∀ _ : Fin 1, Bool)))
    rw [hP]
    exact rectangular_cechObstruction P
  have h1 : rectCoverNumber (Set.univ : Set (∀ _ : Fin 1, Bool)) = 1 :=
    rectCoverNumber_eq_one_iff.mpr
      ⟨⟨fun _ => true, Set.mem_univ _⟩, isRectangle_univ⟩
  rw [h0, h1]
  exact zero_lt_one

/-- **No uniform lower bound**: it is NOT the case that
`ρ(T) ≤ cechObstruction T` for all constraints — rectangles refute it. -/
theorem not_forall_rectCoverNumber_le_cechObstruction :
    ¬ ∀ (V : Type) (A : V → Type) (T : Set (∀ v, A v)),
        rectCoverNumber T ≤ cechObstruction T := by
  intro h
  obtain ⟨V, A, T, hT⟩ := exists_cechObstruction_lt_rectCoverNumber
  exact absurd (h V A T) (not_le.mpr hT)

/-- **No uniform upper bound**: it is NOT the case that
`cechObstruction T ≤ ρ(T)` for all constraints — couplings refute it.
Together with `not_forall_rectCoverNumber_le_cechObstruction`: the raw
Čech obstruction magnitude and the rectangle-cover complexity are
incomparable invariants; the conjectured equality fails in BOTH
directions. -/
theorem not_forall_cechObstruction_le_rectCoverNumber :
    ¬ ∀ (V : Type) (A : V → Type) (T : Set (∀ v, A v)),
        cechObstruction T ≤ rectCoverNumber T := by
  intro h
  obtain ⟨V, A, T, hT⟩ := exists_rectCoverNumber_lt_cechObstruction
  exact absurd (h V A T) (not_le.mpr hT)

/-! ### The origin of the conjecture: the coincidence at the diagonal -/

/-- The two-variable Boolean `diagonal` of `Ste.Sheaf` is the `n = 2`,
`α = Bool` instance of the all-equal coupling. -/
theorem diagonal_eq_allEqual : diagonal = allEqual 2 Bool := by
  ext f
  simp only [diagonal, allEqual, Set.mem_setOf_eq]
  constructor
  · intro hf i j
    have key : ∀ i : Fin 2, f i = f 0 := by
      intro i
      fin_cases i
      · rfl
      · exact hf.symm
    rw [key i, key j]
  · intro hf
    exact hf 0 1

/-- `ρ(diagonal) = 2`: the minimal coupling needs exactly two
rectangles (`{(false,false)}` and `{(true,true)}`). -/
theorem rectCoverNumber_diagonal : rectCoverNumber diagonal = 2 := by
  rw [diagonal_eq_allEqual, rectCoverNumber_allEqual le_rfl,
    Fintype.card_bool]
  rfl

/-- **The coincidence that motivated the conjecture**: at the MINIMAL
nonvanishing instance — the two-variable Boolean diagonal — obstruction
and cover complexity happen to agree: both are `2`.  The preceding
theorems show this equality is an artifact of the smallest example: it
fails already for `allEqual 3 Bool` (`2 < 6`) and in the opposite
direction for every nonempty rectangle (`0 < 1`). -/
theorem diagonal_cechObstruction_eq_rectCoverNumber :
    cechObstruction diagonal = rectCoverNumber diagonal := by
  rw [diagonal_cechObstruction, rectCoverNumber_diagonal]

end STE
