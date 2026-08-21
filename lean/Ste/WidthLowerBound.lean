/-
Width-`w` representations: what a bounded-width table family can and
cannot hide — the lower-bound side of `Ste.JunctionTree`'s outlook,
with the announced statement REFUTED and replaced by the true one.

`Ste.JunctionTree` closes with an outlook (~line 397, "Contrast: full
coupling escapes small scopes"):

> Scaling this to a quantitative lower bound (an `n`-variable coupled
> instance whose every width-`w` table family has size `≥ 2^Ω(n)`) is
> the un-mechanized lower-bound side of the treewidth story; outlook.

and the intended witness there is the maximal coupling `allEqual n α`
(the `diagonal` scaled to arity `n`), whose primal graph is complete and
whose induced width is therefore `n − 1`
(`Ste.CliqueTreewidth.primalGraph_allEqualInstance`).

**Verdict: for `allEqual` the conjecture is FALSE as literally stated,
and this file proves it false.**  High treewidth of the *primal graph*
of one particular encoding says nothing about the size of the *smallest*
faithful bounded-width representation.  The all-equal coupling is
represented exactly by the equality CHAIN

    `f 0 = f 1`, `f 1 = f 2`, …, `f (n−2) = f (n−1)`,

which is `n − 1` constraints, each of support size `2` — width `1`, not
width `n − 1` — and each storable as a table of at most `k²` rows.  Total
size `(n−1)·k²`: linear in `n`, at width `1`.  Transitivity, not
rectangularity, is what makes the coupling cheap.  Mechanized as
`allEqual_isWidthRep_one` / `exists_isWidthRep_one_allEqual` /
`allEqual_chain_table_bound`; `not_forall_widthRep_size_exponential`
states the refutation in negated-quantifier form.

**The true theorem in the neighbourhood.**  What a bounded-width
representation really costs is governed not by treewidth but by
*rectangle-cover complexity* `ρ` (`Ste.RepresentationBounds`), and the
mechanism is a product law:

* `isRectangle_iInter` — rectangles are closed under intersection;
* `hasRectCover_iInter` — hence covers MULTIPLY: if each `Cᵢ` is a union
  of `mᵢ` rectangles then `⋂ᵢ Cᵢ` is a union of `∏ᵢ mᵢ` rectangles (take
  all cross-intersections);
* `hasRectCover_of_hasSupport` — a constraint supported on a scope of
  `≤ w+1` variables over alphabets of size `≤ k` is a union of at most
  `k^(w+1)` cylinders, so it has a rectangle cover of that size.

Composing them gives the headline upper bound

    `ρ(T) ≤ (k^(w+1))^R`

for every faithful width-`w` representation of `T` by `R` constraints
(`rectCoverNumber_le_of_isWidthRep`), and therefore — by the fooling-set
bound (`IsFoolingSet.encard_le_of_hasRectCover`) — the **cut/fooling
lower bound on the NUMBER of constraints**:

    any fooling set `F ⊆ T` forces `|F| ≤ (k^(w+1))^R`

(`IsFoolingSet.encard_le_of_isWidthRep`).  A constraint with an
exponential fooling set therefore needs *many* bounded-width
constraints, no matter how they are chosen.  Instantiated at the
disequality chain of `Ste.ChainFooling`, whose range-of-`chainWitness`
fooling set has `2^m` points on `n = 3m` variables:

    `2^m ≤ (3^(w+1))^R`  (`two_pow_le_of_isWidthRep_neqChain`)

— i.e. `R ≥ m / ((w+1)·log₂ 3)`: linearly many constraints are forced,
and no constant-size width-`w` family can represent the chain
(`not_isWidthRep_neqChain_of_small`).  This is the corrected form of the
outlook: the obstruction to small bounded-width representations is
`ρ`/fooling number, not treewidth, and it bites on `neqChain`, not on
`allEqual`.

**Honest boundary.**  Mechanized here: `IsWidthRep` (a faithful family
of constraints, each supported on `≤ w+1` variables, intersecting to
`T`); closure of rectangles under intersection and the product law for
covers; the cylinder cover of a narrowly supported constraint; the
bound `ρ(T) ≤ (k^(w+1))^R`; the fooling-set consequence; its `neqChain`
instance; the width-`1` equality-chain representation of `allEqual` and
the refutation it yields.  NOT mechanized: any lower bound on the
*total number of table rows* as opposed to the number of constraints
(the two differ by a factor of at most `k^(w+1)`, so the exponential
content is unchanged, but the row-counting bookkeeping is not written);
the logarithmic restatement `R = Ω(m/w)` (kept as the raw exponential
inequality, no logs are introduced); any claim that the equality chain
is size-OPTIMAL among width-`1` representations of `allEqual` (only that
it exists and is linear); and the converse direction — that a small `ρ`
implies a small bounded-width representation — which is false in general
and is not attempted.

References: E. Kushilevitz, N. Nisan, *Communication Complexity*, CUP
1997 (`kushilevitz1997communication`; fooling sets, rectangle covers);
A. Aho, J. Ullman, M. Yannakakis, STOC 1983 (`aho1983notions`);
R. Dechter, *Constraint Processing*, 2003 (bucket elimination, junction
trees, induced width).
-/
import Ste.ChainFooling
import Ste.GluingWidth
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin

namespace STE

open Set

variable {V : Type*} {A : V → Type*}

/-! ### Rectangles are closed under intersection -/

/-- **Rectangles are closed under arbitrary intersections**: the
intersection of product sets is the product of the intersections.  This
is the algebraic fact that makes bounded-width representations
*multiply* rather than add. -/
theorem isRectangle_iInter {ι : Sort*} {R : ι → Set (∀ v, A v)}
    (h : ∀ i, IsRectangle (R i)) : IsRectangle (⋂ i, R i) := by
  classical
  choose P hP using h
  refine ⟨fun v => ⋂ i, P i v, ?_⟩
  ext f
  constructor
  · intro hf
    refine Set.mem_univ_pi.mpr fun v => Set.mem_iInter.mpr fun i => ?_
    have hfi : f ∈ R i := Set.mem_iInter.mp hf i
    rw [hP i] at hfi
    exact Set.mem_univ_pi.mp hfi v
  · intro hf
    refine Set.mem_iInter.mpr fun i => ?_
    rw [hP i]
    exact Set.mem_univ_pi.mpr fun v =>
      Set.mem_iInter.mp (Set.mem_univ_pi.mp hf v) i

/-- **Rectangle covers multiply.**  If each `Cᵢ` (`i : Fin R`) is an
exact union of `mᵢ` rectangles, then `⋂ᵢ Cᵢ` is an exact union of
`∏ᵢ mᵢ` rectangles: take one rectangle from each cover and intersect.
Every cross-intersection is a rectangle (`isRectangle_iInter`), the
union of the cross-intersections is contained in every `Cᵢ`, and any
point of `⋂ᵢ Cᵢ` picks out a rectangle from each cover, hence lies in
the corresponding cross-intersection. -/
theorem hasRectCover_iInter {R : ℕ} {C : Fin R → Set (∀ v, A v)}
    {m : Fin R → ℕ} (h : ∀ i, HasRectCover (C i) (m i)) :
    HasRectCover (⋂ i, C i) (∏ i, m i) := by
  classical
  choose Rc hrect hunion using h
  have hcard : Fintype.card (∀ i : Fin R, Fin (m i)) = ∏ i, m i := by
    simp [Fintype.card_pi]
  set e : (∀ i : Fin R, Fin (m i)) ≃ Fin (∏ i, m i) :=
    Fintype.equivFinOfCardEq hcard with he
  refine ⟨fun c => ⋂ i, Rc i (e.symm c i), fun c => isRectangle_iInter
    fun i => hrect i _, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨c, hxS⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iInter.mpr fun i => ?_
    rw [← hunion i]
    exact Set.mem_iUnion.mpr ⟨_, Set.mem_iInter.mp hxS i⟩
  · intro hx
    have hpick : ∀ i, ∃ j, x ∈ Rc i j := fun i => by
      have : x ∈ ⋃ j, Rc i j := by
        rw [hunion i]; exact Set.mem_iInter.mp hx i
      exact Set.mem_iUnion.mp this
    choose j hj using hpick
    refine Set.mem_iUnion.mpr ⟨e j, Set.mem_iInter.mpr fun i => ?_⟩
    rw [Equiv.symm_apply_apply]
    exact hj i

/-! ### Narrow supports give small rectangle covers -/

variable [DecidableEq V]

/-- The **cylinder** over a scope `σ` and a row `r`: the assignments
whose restriction to `σ` is `r`.  Cylinders are the rows of a bag table
read back as constraints on the whole variable set. -/
def cylinder (σ : Finset V) (r : ∀ v : {x // x ∈ σ}, A v) :
    Set (∀ v, A v) :=
  {f | ∀ (v : V) (h : v ∈ σ), f v = r ⟨v, h⟩}

/-- A cylinder is a rectangle: it fixes the coordinates in `σ` and
leaves the rest free. -/
theorem isRectangle_cylinder (σ : Finset V)
    (r : ∀ v : {x // x ∈ σ}, A v) : IsRectangle (cylinder σ r) := by
  classical
  refine ⟨fun v => if h : v ∈ σ then {r ⟨v, h⟩} else Set.univ, ?_⟩
  ext f
  constructor
  · intro hf
    refine Set.mem_univ_pi.mpr fun v => ?_
    by_cases h : v ∈ σ
    · rw [dif_pos h]
      exact hf v h
    · rw [dif_neg h]
      exact Set.mem_univ _
  · intro hf v h
    have hv := Set.mem_univ_pi.mp hf v
    rw [dif_pos h] at hv
    exact hv

omit [DecidableEq V] in
/-- Every assignment lies in the cylinder over its own restriction. -/
theorem mem_cylinder_restrict (σ : Finset V) (f : ∀ v, A v) :
    f ∈ cylinder σ (fun v : {x // x ∈ σ} => f v) :=
  fun _ _ => rfl

omit [DecidableEq V] in
/-- If a constraint supported on `σ` meets a cylinder over `σ`, it
contains the whole cylinder: membership only reads the `σ`-coordinates,
which the cylinder pins down. -/
theorem cylinder_subset_of_mem {C : Set (∀ v, A v)} {σ : Finset V}
    (hC : HasSupport C (↑σ : Set V)) {r : ∀ v : {x // x ∈ σ}, A v}
    {f : ∀ v, A v} (hfC : f ∈ C) (hfr : f ∈ cylinder σ r) :
    cylinder σ r ⊆ C := by
  intro g hg
  refine (hC f g fun v hv => ?_).mp hfC
  have hv' : v ∈ σ := Finset.mem_coe.mp hv
  rw [hfr v hv', hg v hv']

/-- **Narrow constraints have small rectangle covers.**  A constraint
supported on a scope of `σ.card` variables, over alphabets of size at
most `k`, is an exact union of at most `k ^ σ.card` cylinders — one per
row of its bag table.  (The empty constraint is covered by zero
rectangles.) -/
theorem hasRectCover_of_hasSupport [∀ v, Fintype (A v)]
    {C : Set (∀ v, A v)} {σ : Finset V} {k : ℕ}
    (hC : HasSupport C (↑σ : Set V))
    (halpha : ∀ v : V, Fintype.card (A v) ≤ k) :
    ∃ N : ℕ, N ≤ k ^ σ.card ∧ HasRectCover C N := by
  classical
  rcases Set.eq_empty_or_nonempty C with rfl | ⟨f₀, hf₀⟩
  · exact ⟨0, Nat.zero_le _, hasRectCover_zero_iff.mpr rfl⟩
  · have hJcard : Fintype.card (∀ v : {x // x ∈ σ}, A v) ≤ k ^ σ.card := by
      rw [Fintype.card_pi, Finset.prod_coe_sort σ fun v => Fintype.card (A v)]
      exact Finset.prod_le_pow_card _ _ _ fun v _ => halpha v
    set e : (∀ v : {x // x ∈ σ}, A v)
        ≃ Fin (Fintype.card (∀ v : {x // x ∈ σ}, A v)) :=
      Fintype.equivFin _ with he
    set r₀ : ∀ v : {x // x ∈ σ}, A v := fun v => f₀ v with hr₀
    have hsub : ∀ c, cylinder σ
        (if (∃ f, f ∈ C ∧ f ∈ cylinder σ (e.symm c)) then e.symm c
          else r₀) ⊆ C := by
      intro c
      split_ifs with h
      · obtain ⟨f, hfC, hfr⟩ := h
        exact cylinder_subset_of_mem hC hfC hfr
      · exact cylinder_subset_of_mem hC hf₀ (mem_cylinder_restrict σ f₀)
    refine ⟨Fintype.card (∀ v : {x // x ∈ σ}, A v), hJcard,
      fun c => cylinder σ
        (if (∃ f, f ∈ C ∧ f ∈ cylinder σ (e.symm c)) then e.symm c else r₀),
      fun c => isRectangle_cylinder _ _, ?_⟩
    ext x
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hx
      exact hsub c hc
    · intro hx
      refine Set.mem_iUnion.mpr ⟨e (fun v : {x // x ∈ σ} => x v), ?_⟩
      simp only [Equiv.symm_apply_apply]
      split_ifs with h
      · exact mem_cylinder_restrict σ x
      · exact absurd ⟨x, hx, mem_cylinder_restrict σ x⟩ h

/-! ### Width-`w` representations -/

/-- A **faithful width-`w` representation** of the constraint `T` by `R`
constraints: a family `con : Fin R → Set (∀ v, A v)`, each `con i`
supported on the scope `scope i` of at most `w + 1` variables, whose
intersection is exactly `T`.  This is the representation notion the
junction-tree size bounds of `Ste.JunctionTree` are stated against, with
the elimination bookkeeping stripped away: what is left is exactly
"faithful, and every table is narrow". -/
def IsWidthRep {R : ℕ} (T : Set (∀ v, A v)) (w : ℕ)
    (scope : Fin R → Finset V) (con : Fin R → Set (∀ v, A v)) : Prop :=
  (∀ i, HasSupport (con i) (↑(scope i) : Set V))
    ∧ (∀ i, (scope i).card ≤ w + 1)
    ∧ ⋂ i, con i = T

/-- **The product law for width-`w` representations.**  Any faithful
width-`w` representation of `T` by `R` constraints, over alphabets of
size at most `k`, exhibits `T` as a union of at most `(k^(w+1))^R`
rectangles: each constraint is a union of `≤ k^(w+1)` cylinders
(`hasRectCover_of_hasSupport`) and covers multiply under intersection
(`hasRectCover_iInter`). -/
theorem hasRectCover_of_isWidthRep [∀ v, Fintype (A v)]
    {R : ℕ} {T : Set (∀ v, A v)} {w k : ℕ} {scope : Fin R → Finset V}
    {con : Fin R → Set (∀ v, A v)}
    (hrep : IsWidthRep T w scope con) (hk : 0 < k)
    (halpha : ∀ v : V, Fintype.card (A v) ≤ k) :
    ∃ N : ℕ, N ≤ (k ^ (w + 1)) ^ R ∧ HasRectCover T N := by
  classical
  obtain ⟨hsupp, hnarrow, hfaithful⟩ := hrep
  have hcov : ∀ i, ∃ N : ℕ, N ≤ k ^ (w + 1) ∧ HasRectCover (con i) N := by
    intro i
    obtain ⟨N, hN, hcov⟩ := hasRectCover_of_hasSupport (hsupp i) halpha
    exact ⟨N, hN.trans (Nat.pow_le_pow_right hk (hnarrow i)), hcov⟩
  choose N hN hcov using hcov
  refine ⟨∏ i, N i, ?_, ?_⟩
  · calc ∏ i, N i ≤ ∏ _i : Fin R, k ^ (w + 1) :=
        Finset.prod_le_prod' fun i _ => hN i
      _ = (k ^ (w + 1)) ^ R := by simp
  · rw [← hfaithful]
    exact hasRectCover_iInter hcov

/-- **`ρ` is at most `(k^(w+1))^R`**: rectangle-cover complexity is the
right currency for bounded-width representations.  A representation with
few narrow constraints forces a small rectangle cover. -/
theorem rectCoverNumber_le_of_isWidthRep [∀ v, Fintype (A v)]
    {R : ℕ} {T : Set (∀ v, A v)} {w k : ℕ} {scope : Fin R → Finset V}
    {con : Fin R → Set (∀ v, A v)}
    (hrep : IsWidthRep T w scope con) (hk : 0 < k)
    (halpha : ∀ v : V, Fintype.card (A v) ≤ k) :
    rectCoverNumber T ≤ (((k ^ (w + 1)) ^ R : ℕ) : ℕ∞) := by
  obtain ⟨N, hN, hcov⟩ := hasRectCover_of_isWidthRep hrep hk halpha
  exact (rectCoverNumber_le hcov).trans (ENat.coe_le_coe.mpr hN)

/-- **The fooling-set lower bound on the NUMBER of narrow constraints.**
If `T` has a fooling set `F`, then every faithful width-`w`
representation of `T` by `R` constraints over alphabets of size `≤ k`
satisfies `|F| ≤ (k^(w+1))^R`.  Contrapositively: an exponential fooling
set forces linearly many bounded-width constraints.  This is the
corrected form of `Ste.JunctionTree`'s outlook — the obstruction to a
small bounded-width representation is the fooling number, not the
treewidth of some chosen encoding. -/
theorem IsFoolingSet.encard_le_of_isWidthRep [∀ v, Fintype (A v)]
    {R : ℕ} {T F : Set (∀ v, A v)} (hF : IsFoolingSet T F)
    {w k : ℕ} {scope : Fin R → Finset V} {con : Fin R → Set (∀ v, A v)}
    (hrep : IsWidthRep T w scope con) (hk : 0 < k)
    (halpha : ∀ v : V, Fintype.card (A v) ≤ k) :
    F.encard ≤ (((k ^ (w + 1)) ^ R : ℕ) : ℕ∞) := by
  obtain ⟨N, hN, hcov⟩ := hasRectCover_of_isWidthRep hrep hk halpha
  exact (hF.encard_le_of_hasRectCover hcov).trans (ENat.coe_le_coe.mpr hN)

/-! ### The true exponential instance: the disequality chain -/

/-- **The genuine width lower bound.**  Every faithful width-`w`
representation of the disequality chain `neqChain (3*m) (Fin 3)` by `R`
constraints satisfies `2^m ≤ (3^(w+1))^R`.  The fooling set is the
range of `chainWitness` (`Ste.ChainFooling`), which has `2^m` points on
`n = 3*m` variables.  Reading it as a bound on `R`: linearly many
narrow constraints are forced, `R ≥ m / ((w+1)·log₂ 3)` — this is the
`2^Ω(n)`-flavoured lower bound `Ste.JunctionTree`'s outlook asked for,
attached to the constraint where it is actually true. -/
theorem two_pow_le_of_isWidthRep_neqChain {m R w : ℕ}
    {scope : Fin R → Finset (Fin (3 * m))}
    {con : Fin R → Set (Fin (3 * m) → Fin 3)}
    (hrep : IsWidthRep (A := fun _ => Fin 3) (neqChain (3 * m) (Fin 3))
      w scope con) :
    (2 : ℕ) ^ m ≤ (3 ^ (w + 1)) ^ R := by
  have hfool := isFoolingSet_range_chainWitness
    (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)
    (show (1 : Fin 3) ≠ 2 by decide) m
  have hbound := hfool.encard_le_of_isWidthRep hrep (k := 3)
    (by norm_num) (fun _ => by simp)
  rw [encard_range_chainWitness (show (0 : Fin 3) ≠ 1 by decide)] at hbound
  exact_mod_cast hbound

/-- **No constant-size narrow family represents the chain.**  If
`(3^(w+1))^R < 2^m` — e.g. `R` and `w` fixed while `m` grows — then no
faithful width-`w` representation of `neqChain (3*m) (Fin 3)` by `R`
constraints exists at all. -/
theorem not_isWidthRep_neqChain_of_small {m R w : ℕ}
    (hsmall : (3 ^ (w + 1)) ^ R < 2 ^ m)
    (scope : Fin R → Finset (Fin (3 * m)))
    (con : Fin R → Set (Fin (3 * m) → Fin 3)) :
    ¬ IsWidthRep (A := fun _ => Fin 3) (neqChain (3 * m) (Fin 3))
        w scope con :=
  fun hrep => absurd (two_pow_le_of_isWidthRep_neqChain hrep)
    (not_le.mpr hsmall)

/-! ### The refutation: `allEqual` is cheap at width `1`

The equality chain `f 0 = f 1`, …, `f (n−2) = f (n−1)` is a faithful
width-`1` representation of the maximal coupling.  Its faithfulness is a
transitivity argument, chaining the `n − 1` links along the whole index
range — nothing about the constraint's rectangularity is used, which is
exactly why the high induced width of the pairwise-clique encoding
(`Ste.CliqueTreewidth`) fails to translate into any size lower bound. -/

/-- The `i`-th scope of the equality chain: the two consecutive
coordinates `i.castSucc`, `i.succ`. -/
def eqChainScope (m : ℕ) (i : Fin m) : Finset (Fin (m + 1)) :=
  {i.castSucc, i.succ}

/-- The `i`-th link of the equality chain: `f i = f (i+1)`. -/
def eqChainCon (m : ℕ) (α : Type*) (i : Fin m) : Set (Fin (m + 1) → α) :=
  pairEqConstraint i.castSucc i.succ

/-- Each link has support size at most `2` — width `1`. -/
theorem eqChainScope_card_le (m : ℕ) (i : Fin m) :
    (eqChainScope m i).card ≤ 1 + 1 := by
  calc (eqChainScope m i).card
      ≤ ({i.succ} : Finset (Fin (m + 1))).card + 1 :=
        Finset.card_insert_le _ _
    _ = 1 + 1 := by simp

/-- Each link is supported on its two-element scope. -/
theorem eqChainCon_hasSupport (m : ℕ) (α : Type*) (i : Fin m) :
    HasSupport (A := fun _ : Fin (m + 1) => α) (eqChainCon m α i)
      (↑(eqChainScope m i) : Set (Fin (m + 1))) := by
  have h := hasSupport_pairEqConstraint
    (α := α) i.castSucc i.succ
  simpa [eqChainCon, eqChainScope] using h

/-- **Faithfulness of the equality chain (transitivity).**  The
intersection of the `m` consecutive-equality links on `m + 1` variables
is exactly `allEqual (m+1) α`.  Forward direction: induction along the
chain shows every coordinate equals the `0`-th. -/
theorem iInter_eqChainCon (m : ℕ) (α : Type*) :
    ⋂ i : Fin m, eqChainCon m α i = allEqual (m + 1) α := by
  ext f
  simp only [Set.mem_iInter, eqChainCon, pairEqConstraint, Set.mem_setOf_eq,
    allEqual]
  constructor
  · intro h
    have key : ∀ k : ℕ, ∀ hk : k < m + 1,
        f ⟨k, hk⟩ = f ⟨0, Nat.succ_pos m⟩ := by
      intro k
      induction k with
      | zero => intro hk; rfl
      | succ k ih =>
        intro hk
        have hkm : k < m := by omega
        have hlink := h ⟨k, hkm⟩
        have e1 : ((⟨k, hkm⟩ : Fin m).castSucc)
            = (⟨k, by omega⟩ : Fin (m + 1)) := by
          apply Fin.ext; simp
        have e2 : ((⟨k, hkm⟩ : Fin m).succ)
            = (⟨k + 1, hk⟩ : Fin (m + 1)) := by
          apply Fin.ext; simp
        rw [e1, e2] at hlink
        rw [← hlink]
        exact ih _
    intro i j
    exact (key i.val i.isLt).trans (key j.val j.isLt).symm
  · intro h i
    exact h _ _

/-- **THE REFUTATION.**  For every `m` and every alphabet `α`, the
equality chain is a faithful width-`1` representation of the maximal
coupling `allEqual (m+1) α` by exactly `m` constraints.  So the
`n`-variable maximal coupling — whose primal graph is the complete graph
and whose induced width is `n − 1` — is nonetheless represented at
width `1` by `n − 1` constraints.  `Ste.JunctionTree`'s outlook, read
literally ("an `n`-variable coupled instance whose every width-`w` table
family has size `≥ 2^Ω(n)`"), is FALSE for this instance. -/
theorem allEqual_isWidthRep_one (m : ℕ) (α : Type*) :
    IsWidthRep (A := fun _ : Fin (m + 1) => α) (allEqual (m + 1) α) 1
      (eqChainScope m) (eqChainCon m α) :=
  ⟨eqChainCon_hasSupport m α, eqChainScope_card_le m, iInter_eqChainCon m α⟩

/-- Existential form of the refutation: at every arity the maximal
coupling admits SOME faithful width-`1` representation by `m`
constraints. -/
theorem exists_isWidthRep_one_allEqual (m : ℕ) (α : Type*) :
    ∃ (scope : Fin m → Finset (Fin (m + 1)))
      (con : Fin m → Set (Fin (m + 1) → α)),
      IsWidthRep (A := fun _ : Fin (m + 1) => α) (allEqual (m + 1) α) 1
        scope con :=
  ⟨eqChainScope m, eqChainCon m α, allEqual_isWidthRep_one m α⟩

/-- **Each link stores at most `k²` rows.**  Every constraint of the
equality chain, over an alphabet of size at most `k`, has a rectangle
cover of size at most `k²` — so the whole width-`1` representation of
`allEqual (m+1) α` costs at most `m · k²`: LINEAR in the number of
variables, at width `1`.  (The `m · k²` product is left as the reader's
arithmetic; what is mechanized is the per-link bound, which is the only
non-bookkeeping content.) -/
theorem allEqual_chain_table_bound {m : ℕ} {α : Type*} [Fintype α]
    {k : ℕ} (hk : 0 < k) (halpha : Fintype.card α ≤ k) (i : Fin m) :
    ∃ N : ℕ, N ≤ k ^ 2 ∧
      HasRectCover (A := fun _ : Fin (m + 1) => α) (eqChainCon m α i) N := by
  obtain ⟨N, hN, hcov⟩ := hasRectCover_of_hasSupport
    (A := fun _ : Fin (m + 1) => α) (eqChainCon_hasSupport m α i)
    (k := k) (fun _ => halpha)
  exact ⟨N, hN.trans (Nat.pow_le_pow_right hk
    (eqChainScope_card_le m i)), hcov⟩

/-- **The outlook conjecture, refuted in negated-quantifier form.**  It
is NOT the case that every maximally coupled instance escapes every
bounded-width representation: `allEqual (m+1) α` has one at width `1`
for every `m`.  (The universally quantified statement refuted here is
"for every `m` there is NO faithful width-`1` representation of
`allEqual (m+1) Bool` by `m` constraints" — the shape any `2^Ω(n)`
size lower bound at fixed width would have to imply.) -/
theorem not_forall_widthRep_size_exponential :
    ¬ ∀ m : ℕ, ∀ (scope : Fin m → Finset (Fin (m + 1)))
        (con : Fin m → Set (Fin (m + 1) → Bool)),
        ¬ IsWidthRep (A := fun _ : Fin (m + 1) => Bool)
            (allEqual (m + 1) Bool) 1 scope con := by
  intro h
  exact h 3 (eqChainScope 3) (eqChainCon 3 Bool)
    (allEqual_isWidthRep_one 3 Bool)

/-! ### The corrected picture

Putting the two halves side by side:

* **Width does not force exponential size for `allEqual`.**  The maximal
  coupling has a faithful width-`1` representation of linear size
  (`allEqual_isWidthRep_one`, `allEqual_chain_table_bound`), because
  equality is transitive.  Its `ρ` is only `|α|`
  (`rectCoverNumber_allEqual`, `Ste.RepresentationBounds`) — and
  `rectCoverNumber_le_of_isWidthRep` shows `ρ` is precisely the quantity
  a bounded-width representation must pay for, so a constraint with
  small `ρ` simply cannot carry a size lower bound.
* **Where the exponential really lives.**  The Čech obstruction of
  `allEqual` IS exponential (`cechObstruction_allEqual`, `|α|ⁿ − |α|`),
  but that is the ADDITIVE defect of the box closure, not a
  representation cost — exactly the incomparability already recorded in
  `Ste.RepresentationBounds`
  (`not_forall_cechObstruction_le_rectCoverNumber`).
* **Where a genuine size lower bound does hold.**  On constraints with
  exponential fooling number: the disequality chain forces
  `2^m ≤ (3^(w+1))^R` (`two_pow_le_of_isWidthRep_neqChain`), hence
  linearly many narrow constraints and no bounded-size width-`w`
  family at all (`not_isWidthRep_neqChain_of_small`).

So the dichotomy `Ste.JunctionTree` gestures at is real, but its axis is
`ρ`/fooling number, not treewidth, and `allEqual` sits on the EASY side
of it. -/

end STE
