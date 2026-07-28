/-
The fooling-set bound for the disequality chain — discharging the open
half of the conjecture "$\rectrho$ vs. width incomparability, other
direction" (papers/papers/ste-cohomology.tex, ~line 1085,
`\begin{conjecture}[\rectrho vs. width incomparability, other
direction; not mechanized]`, restated in §"What remains conjectural"):

> A width-1 chain of disequality constraints over an alphabet of size
> `k ≥ 3` on `n` variables has feasible set of size `k(k-1)^{n-1}` and,
> we conjecture, `ρ = 2^{Ω(n)}` (a fooling-set construction along
> alternating assignments looks plausible).

This file builds exactly that fooling-set construction and mechanizes
the bound.  The chain `neqChain n α` (`{f | ∀ i, f i ≠ f (i+1)}`) is the
width-1 disequality chain of the conjecture: consecutive coordinates
(under the ℕ-valued successor relation, which sidesteps `Fin.castSucc`
bookkeeping) must differ.

**The construction.**  For chain length `n = 3 * m` and three distinct
alphabet symbols `a b c`, cut the chain into `m` consecutive blocks of
three coordinates `(3q, 3q+1, 3q+2)`.  Block `q` is filled with the
pattern `(a, b, c)` if `bits q = false` and `(b, a, c)` if `bits q =
true` — the separator `c` at the end of every block guarantees
consecutive blocks never clash regardless of the neighboring bits, and
within a block the two orderings of `a, b` are exactly the "alternating
assignment" the conjecture's prose anticipates.  This gives an
injective map `chainWitness a b c m : (Fin m → Bool) → (Fin (3*m) → α)`
landing inside `neqChain (3*m) α` (`chainWitness_mem`,
`chainWitness_injective`).

**Why it fools every rectangle.**  Given two bit vectors differing at
block `q`, mixing their witnesses along the predicate `v ≤ 3*q` (the
engine `IsRectangle.mix_mem`, `Ste.RepresentationBounds`) produces a
hybrid that agrees with the first witness through coordinate `3*q` and
with the second from `3*q+1` on.  But those two coordinates are exactly
the first two slots of block `q`, which the two bit assignments fill in
opposite order — so the hybrid repeats a value across the boundary
`(3*q, 3*q+1)`, leaving `neqChain`.  Hence any rectangle contained in
`neqChain` can hold at most one witness per bit vector: the range of
`chainWitness` is a fooling set (`isFoolingSet_range_chainWitness`).

**The bound.**  `chainWitness` is injective on `2^m` bit vectors
(`encard_range_chainWitness`), so by the fooling-set lower bound
(`IsFoolingSet.encard_le_of_hasRectCover`,
`Ste.RepresentationBounds.le_rectCoverNumber`):
`2^m ≤ ρ(neqChain (3*m) α)` for any alphabet with three distinct
elements (`two_pow_le_rectCoverNumber_neqChain`, instantiated concretely
at `Fin 3` in `two_pow_le_rectCoverNumber_neqChain_fin3`).  Writing the
chain length as `n = 3*m`, this is `ρ = 2^{Ω(n)}` — the fooling-set half
of the conjecture, mechanized.  (The companion feasible-set count
`k(k-1)^{n-1}` and the sharper base implicit in "alternating
assignments" are NOT pursued here — see the module docstring's honest
boundary below.)

**Honest boundary.**  Mechanized: `neqChain`; the witness construction
`chainWitness` and its membership and injectivity; the fooling-set
property of its range; the resulting bound `2^m ≤ ρ(neqChain (3*m) α)`
for any `α` with three distinct elements, and its `Fin 3` instance.
NOT mechanized: the exact feasible-set cardinality `k(k-1)^{n-1}`; any
matching upper bound on `ρ` (only the conjectured lower bound is at
stake); the general-`k`-from-`Fintype.card` packaging is included only
as far as it falls out cleanly (`two_pow_le_rectCoverNumber_neqChain`
already covers every 3-element-or-larger alphabet via any three
witnesses `a ≠ b`, `a ≠ c`, `b ≠ c`, so no separate extraction lemma is
needed).

References: E. Kushilevitz, N. Nisan, *Communication Complexity*, CUP
1997 (`kushilevitz1997communication`; fooling sets, §1.3); A. Aho,
J. Ullman, M. Yannakakis, STOC 1983 (`aho1983notions`; origin of
rectangle covers and fooling sets).
-/
import Ste.RepresentationBounds

namespace STE

open Set

/-! ### The width-1 disequality chain -/

/-- The **width-1 disequality chain**: assignments to `Fin n → α` under
which every pair of ℕ-successor coordinates must differ.  This is the
chain of the conjecture "`ρ` vs. width incomparability, other
direction" (papers/papers/ste-cohomology.tex, ~line 1085): a chain of
binary disequality constraints, treewidth (as a path) `1`. -/
def neqChain (n : ℕ) (α : Type*) : Set (Fin n → α) :=
  {f | ∀ i j : Fin n, (i : ℕ) + 1 = (j : ℕ) → f i ≠ f j}

variable {α : Type*}

/-! ### The fooling witness -/

/-- The fooling witness on a chain of length `3 * m`: cut the chain into
`m` blocks of three coordinates.  Block `q` reads `(a, b, c)` if
`bits q = false` and `(b, a, c)` if `bits q = true` — the trailing `c`
separates consecutive blocks regardless of their bits, and the leading
two slots realize the "alternating assignment" of the two orderings of
`a, b`. -/
def chainWitness (a b c : α) (m : ℕ) (bits : Fin m → Bool) :
    Fin (3 * m) → α :=
  fun i =>
    if i.val % 3 = 0 then
      (if bits ⟨i.val / 3, by have := i.isLt; omega⟩ then b else a)
    else if i.val % 3 = 1 then
      (if bits ⟨i.val / 3, by have := i.isLt; omega⟩ then a else b)
    else c

variable {a b c : α} {m : ℕ}

/-- Evaluation at the first slot of block `q`: `a` if the bit is
`false`, `b` if `true`. -/
theorem chainWitness_val_zero (bits : Fin m → Bool) (i : Fin (3 * m)) (q : ℕ)
    (hq : q < m) (hi : i.val = 3 * q) :
    chainWitness a b c m bits i = if bits ⟨q, hq⟩ then b else a := by
  have h1 : i.val % 3 = 0 := by omega
  have h2 : i.val / 3 = q := by omega
  simp [chainWitness, h1, h2]

/-- Evaluation at the second slot of block `q`: `b` if the bit is
`false`, `a` if `true` — the opposite of the first slot. -/
theorem chainWitness_val_one (bits : Fin m → Bool) (i : Fin (3 * m)) (q : ℕ)
    (hq : q < m) (hi : i.val = 3 * q + 1) :
    chainWitness a b c m bits i = if bits ⟨q, hq⟩ then a else b := by
  have h1 : i.val % 3 = 1 := by omega
  have h2 : i.val / 3 = q := by omega
  simp [chainWitness, h1, h2]

/-- Evaluation at the third slot of block `q`: always `c`. -/
theorem chainWitness_val_two (bits : Fin m → Bool) (i : Fin (3 * m)) (q : ℕ)
    (_hq : q < m) (hi : i.val = 3 * q + 2) :
    chainWitness a b c m bits i = c := by
  have h1 : i.val % 3 = 2 := by omega
  simp [chainWitness, h1]

/-! ### Membership and injectivity -/

/-- The witness lies in the disequality chain: consecutive coordinates
always differ.  Within a block the two values are `{a, b}` in one
order or the other (distinct by `hab`); crossing to the separator hits
`c` (distinct by `hac`/`hbc`); crossing from a separator into the next
block reads the next block's first slot, again in `{a, b}` (distinct
from `c` by `hac`/`hbc` symmetrically). -/
theorem chainWitness_mem (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (bits : Fin m → Bool) :
    chainWitness a b c m bits ∈ neqChain (3 * m) α := by
  rintro i j hij
  have hjlt := j.isLt
  have hilt := i.isLt
  have hqi : i.val / 3 < m := by omega
  set q := i.val / 3 with hqdef
  have hr : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
  rcases hr with hr | hr | hr
  · -- i is the first slot of block q; j is the second slot of block q
    have hiv : i.val = 3 * q := by omega
    have hjv : j.val = 3 * q + 1 := by omega
    rw [chainWitness_val_zero bits i q hqi hiv,
      chainWitness_val_one bits j q hqi hjv]
    rcases Bool.eq_false_or_eq_true (bits ⟨q, hqi⟩) with hbit | hbit <;>
      simp [hbit, hab, hab.symm]
  · -- i is the second slot of block q; j is the third slot (separator)
    have hiv : i.val = 3 * q + 1 := by omega
    have hjv : j.val = 3 * q + 2 := by omega
    rw [chainWitness_val_one bits i q hqi hiv, chainWitness_val_two bits j q hqi hjv]
    rcases Bool.eq_false_or_eq_true (bits ⟨q, hqi⟩) with hbit | hbit <;>
      simp [hbit, hbc, hac]
  · -- i is the separator of block q; j is the first slot of block q+1
    have hqi1 : q + 1 < m := by omega
    have hiv : i.val = 3 * q + 2 := by omega
    have hjv : j.val = 3 * (q + 1) := by omega
    rw [chainWitness_val_two bits i q hqi hiv,
      chainWitness_val_zero bits j (q + 1) hqi1 hjv]
    rcases Bool.eq_false_or_eq_true (bits ⟨q + 1, hqi1⟩) with hbit | hbit <;>
      simp [hbit, hac.symm, hbc.symm]

/-- `chainWitness` is injective (needs only `a ≠ b`): two bit vectors
that differ at block `q` produce witnesses that differ at coordinate
`3 * q`, since `chainWitness_val_zero` reads the bit back as `a` versus
`b`. -/
theorem chainWitness_injective (hab : a ≠ b) :
    Function.Injective (chainWitness a b c m) := by
  intro bits₁ bits₂ h
  funext q
  by_contra hne
  have hival : (3 * q.val : ℕ) = 3 * q.val := rfl
  have hval : chainWitness a b c m bits₁ (⟨3 * q.val, by have := q.isLt; omega⟩ : Fin (3 * m))
      = chainWitness a b c m bits₂ (⟨3 * q.val, by have := q.isLt; omega⟩ : Fin (3 * m)) :=
    congrFun h _
  rw [chainWitness_val_zero bits₁ _ q.val q.isLt hival,
    chainWitness_val_zero bits₂ _ q.val q.isLt hival] at hval
  rcases Bool.eq_false_or_eq_true (bits₁ q) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (bits₂ q) with h2 | h2 <;>
    simp_all

/-! ### The fooling set -/

/-- **The fooling set for the disequality chain**: the range of
`chainWitness` fools every sub-rectangle of `neqChain (3*m) α`.  Given
two witnesses whose bit vectors differ at block `q`, mixing them along
`v ≤ 3*q` (`IsRectangle.mix_mem`) glues the first witness's value at
coordinate `3*q` to the second witness's value at coordinate `3*q+1` —
by `chainWitness_val_zero`/`chainWitness_val_one` these coincide
(`false`/`true` land on `a`/`b` in opposite order across the two bit
vectors), so the mix repeats a value across a chain edge and cannot lie
in `neqChain`, contradicting that the ambient rectangle is a
sub-rectangle of `neqChain`. -/
theorem isFoolingSet_range_chainWitness (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (m : ℕ) :
    IsFoolingSet (neqChain (3 * m) α) (Set.range (chainWitness a b c m)) := by
  classical
  refine ⟨?_, ?_⟩
  · rintro f ⟨bits, rfl⟩
    exact chainWitness_mem hab hac hbc bits
  · rintro R hR hRT f ⟨bits₁, rfl⟩ g ⟨bits₂, rfl⟩ hfR hgR
    suffices h : bits₁ = bits₂ by rw [h]
    by_contra hne
    obtain ⟨q, hq⟩ := Function.ne_iff.mp hne
    have hqlt := q.isLt
    have hb1 : (3 * q.val : ℕ) < 3 * m := by omega
    have hb2 : (3 * q.val + 1 : ℕ) < 3 * m := by omega
    set mix : Fin (3 * m) → α :=
      fun v => if v.val ≤ 3 * q.val then chainWitness a b c m bits₁ v
        else chainWitness a b c m bits₂ v with hmixdef
    have hmixR : mix ∈ R := hR.mix_mem hfR hgR (fun v => v.val ≤ 3 * q.val)
    have hmixT : mix ∈ neqChain (3 * m) α := hRT hmixR
    have hij : ((⟨3 * q.val, hb1⟩ : Fin (3 * m)) : ℕ) + 1
        = ((⟨3 * q.val + 1, hb2⟩ : Fin (3 * m)) : ℕ) := by simp
    have hne' := hmixT ⟨3 * q.val, hb1⟩ ⟨3 * q.val + 1, hb2⟩ hij
    apply hne'
    have hmixval1 : mix ⟨3 * q.val, hb1⟩ = chainWitness a b c m bits₁ ⟨3 * q.val, hb1⟩ := by
      simp only [hmixdef]
      rw [if_pos le_rfl]
    have hmixval2 : mix ⟨3 * q.val + 1, hb2⟩ = chainWitness a b c m bits₂ ⟨3 * q.val + 1, hb2⟩ := by
      simp only [hmixdef]
      rw [if_neg (by omega)]
    rw [hmixval1, hmixval2,
      chainWitness_val_zero bits₁ ⟨3 * q.val, hb1⟩ q.val hqlt rfl,
      chainWitness_val_one bits₂ ⟨3 * q.val + 1, hb2⟩ q.val hqlt rfl]
    rcases Bool.eq_false_or_eq_true (bits₁ q) with h1 | h1 <;>
      rcases Bool.eq_false_or_eq_true (bits₂ q) with h2 | h2 <;>
      simp_all

/-! ### Cardinality of the fooling set -/

/-- The fooling set has exactly `2^m` points: `chainWitness` is
injective, and there are `2^m` bit vectors `Fin m → Bool`. -/
theorem encard_range_chainWitness (hab : a ≠ b) :
    (Set.range (chainWitness a b c m)).encard = ((2 ^ m : ℕ) : ℕ∞) := by
  rw [← Set.image_univ, (chainWitness_injective hab).encard_image,
    Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]

/-! ### Headline bounds -/

/-- **The fooling number of the disequality chain is exponential**: for
any alphabet with three distinct elements `a, b, c`, the chain of
length `3*m` has `foolingNumber ≥ 2^m`. This is the fooling-set half of
the conjecture "`ρ` vs. width incomparability, other direction"
(papers/papers/ste-cohomology.tex, ~line 1085): a width-1 chain of
disequality constraints on `n = 3*m` variables over an alphabet of size
`k ≥ 3` has `ρ = 2^{Ω(n)}`. -/
theorem two_pow_le_foolingNumber_neqChain {a b c : α} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (m : ℕ) :
    ((2 ^ m : ℕ) : ℕ∞) ≤ foolingNumber (neqChain (3 * m) α) := by
  rw [← encard_range_chainWitness (a := a) (b := b) (c := c) hab]
  exact (isFoolingSet_range_chainWitness hab hac hbc m).le_foolingNumber

/-- **The rectangle-cover number of the disequality chain is
exponential — the conjecture's fooling-set bound, mechanized**: for any
alphabet with three distinct elements `a, b, c`, the width-1
disequality chain of length `n = 3*m` has `ρ(neqChain n α) ≥ 2^m =
2^{n/3} = 2^{Ω(n)}`.  This discharges "a fooling-set construction along
alternating assignments looks plausible" (papers/papers/ste-cohomology.tex,
~line 1085 and §"What remains conjectural"): the alternating-assignment
construction is `chainWitness`, and its range is the fooling set
(`isFoolingSet_range_chainWitness`) that forces the bound via
`IsFoolingSet.encard_le_of_hasRectCover` / `le_rectCoverNumber`
(`Ste.RepresentationBounds`). -/
theorem two_pow_le_rectCoverNumber_neqChain {a b c : α} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (m : ℕ) :
    ((2 ^ m : ℕ) : ℕ∞) ≤ rectCoverNumber (neqChain (3 * m) α) := by
  rw [← encard_range_chainWitness (a := a) (b := b) (c := c) hab]
  exact le_rectCoverNumber fun _ hm =>
    (isFoolingSet_range_chainWitness hab hac hbc m).encard_le_of_hasRectCover hm

/-- **Concrete instance**: at the smallest witnessing alphabet `Fin 3`,
the disequality chain of length `3*m` needs at least `2^m` rectangles
to cover exactly. -/
theorem two_pow_le_rectCoverNumber_neqChain_fin3 (m : ℕ) :
    ((2 ^ m : ℕ) : ℕ∞) ≤ rectCoverNumber (neqChain (3 * m) (Fin 3)) :=
  two_pow_le_rectCoverNumber_neqChain
    (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)
    (show (1 : Fin 3) ≠ 2 by decide) m

end STE
