/-
General-`k` strengthening of `shannonDist_inf_not_contraction`.

`Ste.InfoTopology.shannonDist_inf_not_contraction` exhibits a single `Fin 4`
instance witnessing that the lattice meet `⊓` is not a metric contraction for
the combinatorial Shannon distance `shannonDist`. This module upgrades that
single witness to a *scaling* family: for every candidate Lipschitz constant
`C` there is a carrier `Fin (2 * (C + 1))` and partitions `P, Q, R` on it with
`shannonDist P Q = 1` but `shannonDist (P ⊓ R) (Q ⊓ R) = C + 1`, so no
constant `C` can uniformly bound the distortion `⊓` introduces. This is the
quantitative form of the Gács–Körner discontinuity already flagged (but only
instantiated at `k = 2`) in `Ste.InfoTopology`.

The witness, for `k := C + 1` and `n := 2 * k`, on `Fin n`:
* `P := ⊤` (one block);
* `Q := Setoid.ker (fun i => decide (i.val < k))`, the two halves
  `{0,…,k-1}` and `{k,…,2k-1}`;
* `R := Setoid.ker (fun i => i.val % k)`, the perfect matching pairing `i`
  with `i + k` (as `Fin k`-valued residues).

Then `P ⊓ R = R` (since `P = ⊤`) has rank `k`, while `Q ⊓ R = ⊥` (the two
kernel maps together are injective) has rank `0`; meanwhile `shannonDist P Q
= rank P - rank Q = 1`. So meeting with `R` inflates a distance-`1` pair to a
distance-`k` pair, for arbitrarily large `k`.
-/
import Ste.InfoTopology

namespace STE.PartitionRank

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable section

open scoped Classical

/-! ## Part 1: block count of a kernel of a surjective map -/

/-- The block count of the kernel partition of a surjective map onto a
finite type is the cardinality of the codomain: the fibers of `f` are
exactly the blocks. -/
theorem blockCount_ker_of_surjective {f : α → β} (hf : Function.Surjective f) :
    blockCount (Setoid.ker f) = Fintype.card β :=
  Fintype.card_congr (Setoid.quotientKerEquivOfSurjective f hf)

/-! ## Part 2: the meet of two kernels is the kernel of the pair map -/

omit [Fintype α] [Fintype β] in
/-- The meet of two kernel partitions is the kernel of the pair map: `x` and
`y` are related by `ker f ⊓ ker g` exactly when `f x = f y` and `g x = g y`,
i.e. exactly when `(f x, g x) = (f y, g y)`. -/
theorem ker_inf_ker (f : α → β) {γ : Type*} (g : α → γ) :
    Setoid.ker f ⊓ Setoid.ker g = Setoid.ker (fun x => (f x, g x)) := by
  apply Setoid.ext
  intro x y
  simp only [Setoid.inf_iff_and, Setoid.ker_def, Prod.mk.injEq]

omit [Fintype α] [Fintype β] in
/-- If the pair map `x ↦ (f x, g x)` is injective, the meet of the two
kernels collapses to the discrete partition `⊥`. -/
theorem ker_inf_ker_eq_bot_of_injective (f : α → β) {γ : Type*} (g : α → γ)
    (hinj : Function.Injective (fun x => (f x, g x))) :
    Setoid.ker f ⊓ Setoid.ker g = ⊥ := by
  rw [ker_inf_ker]
  exact Setoid.ker_eq_bot_iff.mpr hinj

/-! ## Part 3: the witness family -/

/-- The "halves" map on `Fin n` used to build `Q` in `meetWitness`: `true` on
the first `k` points, `false` on the rest. -/
def halvesMap (k n : ℕ) (i : Fin n) : Bool := decide (i.val < k)

/-- The "matching" map on `Fin n` used to build `R` in `meetWitness`: the
residue of `i` modulo `k`, pairing `i` with `i + k`. -/
def matchMap (k n : ℕ) (hk : 0 < k) (i : Fin n) : Fin k :=
  ⟨i.val % k, Nat.mod_lt _ hk⟩

variable (k : ℕ) (hk : 0 < k)

/-- `halvesMap` is surjective onto `Bool` on `Fin (2 * k)` once `k ≥ 1`: both
`0` and `k` lie in the carrier, landing in the two different halves. -/
theorem halvesMap_surjective (hk : 0 < k) : Function.Surjective (halvesMap k (2 * k)) := by
  intro b
  cases b with
  | false =>
      refine ⟨⟨k, by omega⟩, ?_⟩
      simp [halvesMap]
  | true =>
      refine ⟨⟨0, by omega⟩, ?_⟩
      simp only [halvesMap, decide_eq_true_eq]
      exact hk

/-- `matchMap` is surjective onto `Fin k` on `Fin (2 * k)`: every residue
`r < k` is hit by the point `i = r` itself. -/
theorem matchMap_surjective : Function.Surjective (matchMap k (2 * k) hk) := by
  intro r
  refine ⟨⟨r.val, by omega⟩, ?_⟩
  apply Fin.ext
  show r.val % k = r.val
  exact Nat.mod_eq_of_lt r.isLt

/-- The pair `(halvesMap, matchMap)` is jointly injective on `Fin (2 * k)`:
knowing which half a point is in and its residue mod `k` pins it down
exactly, since each half is a complete residue system mod `k`. -/
theorem halvesMap_matchMap_injective :
    Function.Injective
      (fun i : Fin (2 * k) => (halvesMap k (2 * k) i, matchMap k (2 * k) hk i)) := by
  intro x y hxy
  simp only [Prod.mk.injEq, halvesMap, matchMap, decide_eq_decide, Fin.mk.injEq] at hxy
  obtain ⟨hiff, hmod⟩ := hxy
  apply Fin.ext
  by_cases hx : x.val < k
  · have hy : y.val < k := hiff.mp hx
    have hxm : x.val % k = x.val := Nat.mod_eq_of_lt hx
    have hym : y.val % k = y.val := Nat.mod_eq_of_lt hy
    omega
  · have hy : ¬ y.val < k := fun h => hx (hiff.mpr h)
    have hx' : k ≤ x.val := by omega
    have hy' : k ≤ y.val := by omega
    have hxm : x.val % k = x.val - k := by
      rw [Nat.mod_eq_sub_mod hx', Nat.mod_eq_of_lt (by omega)]
    have hym : y.val % k = y.val - k := by
      rw [Nat.mod_eq_sub_mod hy', Nat.mod_eq_of_lt (by omega)]
    omega

/-- The scaling witness on `Fin (2 * k)`: `P = ⊤`, `Q` splits the carrier
into its two halves, `R` is the perfect matching pairing `i` with `i + k`. -/
def meetWitnessP : Setoid (Fin (2 * k)) := ⊤

def meetWitnessQ : Setoid (Fin (2 * k)) := Setoid.ker (halvesMap k (2 * k))

def meetWitnessR : Setoid (Fin (2 * k)) := Setoid.ker (matchMap k (2 * k) hk)

theorem blockCount_meetWitnessQ (hk : 0 < k) : blockCount (meetWitnessQ k) = 2 := by
  rw [meetWitnessQ, blockCount_ker_of_surjective (halvesMap_surjective k hk), Fintype.card_bool]

theorem blockCount_meetWitnessR : blockCount (meetWitnessR k hk) = k := by
  rw [meetWitnessR, blockCount_ker_of_surjective (matchMap_surjective k hk), Fintype.card_fin]

theorem meetWitnessP_inf_meetWitnessR : meetWitnessP k ⊓ meetWitnessR k hk = meetWitnessR k hk :=
  top_inf_eq (meetWitnessR k hk)

theorem meetWitnessQ_inf_meetWitnessR : meetWitnessQ k ⊓ meetWitnessR k hk = ⊥ :=
  ker_inf_ker_eq_bot_of_injective _ _ (halvesMap_matchMap_injective k hk)

/-- The two headline distances of the scaling witness: `shannonDist P Q = 1`
throughout the family, while `shannonDist (P ⊓ R) (Q ⊓ R) = k` grows without
bound. -/
theorem shannonDist_meetWitness_eq :
    shannonDist (meetWitnessP k) (meetWitnessQ k) = 1 ∧
    shannonDist (meetWitnessP k ⊓ meetWitnessR k hk) (meetWitnessQ k ⊓ meetWitnessR k hk) = k := by
  haveI hne : Nonempty (Fin (2 * k)) := ⟨⟨0, by omega⟩⟩
  have hcard : Fintype.card (Fin (2 * k)) = 2 * k := Fintype.card_fin (2 * k)
  have hbcQ : blockCount (meetWitnessQ k) = 2 := blockCount_meetWitnessQ k hk
  have hbcR : blockCount (meetWitnessR k hk) = k := blockCount_meetWitnessR k hk
  have hrQ : rank (meetWitnessQ k) = 2 * k - 2 := by unfold rank; rw [hbcQ, hcard]
  have hrR : rank (meetWitnessR k hk) = 2 * k - k := by unfold rank; rw [hbcR, hcard]
  have hrtop : rank (⊤ : Setoid (Fin (2 * k))) = 2 * k - 1 := by rw [rank_top, hcard]
  constructor
  · rw [meetWitnessP, shannonDist_top, hrtop, hrQ]
    omega
  · rw [meetWitnessP_inf_meetWitnessR, meetWitnessQ_inf_meetWitnessR,
      shannonDist_comm, shannonDist_bot]
    omega

end

/-! ## Part 4: the packaged theorem -/

/-- The general-`k` strengthening of `shannonDist_inf_not_contraction`: meet
`⊓` admits *no* uniform Lipschitz constant for the combinatorial Shannon
distance. For every candidate constant `C` there is a finite carrier and
partitions `P, Q, R` on it — `P = ⊤`, `Q` the two-halves partition, `R` the
perfect matching, on `Fin (2 * (C + 1))` — with `shannonDist P Q = 1` but
`shannonDist (P ⊓ R) (Q ⊓ R) = C + 1 > C`, so `C` fails as a Lipschitz bound
for `⊓`. This is the quantitative form of the Gács–Körner discontinuity
(Delsol Prop. 19) already witnessed at `k = 2` by
`shannonDist_inf_not_contraction`. -/
theorem meet_not_lipschitz :
    ∀ C : ℕ, ∃ (n : ℕ) (P Q R : Setoid (Fin n)),
      C * shannonDist P Q < shannonDist (P ⊓ R) (Q ⊓ R) := by
  intro C
  set k := C + 1 with hkdef
  have hk : 0 < k := by omega
  refine ⟨2 * k, meetWitnessP k, meetWitnessQ k, meetWitnessR k hk, ?_⟩
  obtain ⟨hd1, hd2⟩ := shannonDist_meetWitness_eq k hk
  rw [hd1, hd2]
  omega

end STE.PartitionRank
