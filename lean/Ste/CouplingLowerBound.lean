/-
The hard side of the tractability dichotomy: unbounded coupling forces
an exponential representation gap.

`Ste.CechObstruction` computes the concrete Čech obstruction of the
singleton cover — the count of compatible-but-stuck families of local
sections — and shows it vanishes on rectangles and is `2` on the
two-variable Boolean `diagonal`.  This file scales that witness to `n`
variables and closes the quantitative lower-bound side of the
dichotomy that `Ste.JunctionTree` leaves as outlook.

**The characterization.**  First, the singleton-cover half of the
presheaf gluing conjecture is closed as an iff
(`cechVanishes_iff_rectangular`): the Čech obstruction of the
singleton cover vanishes *exactly* when the constraint is a rectangle
`univ.pi P`.  Forward is `rectangular_of_cechVanishes`; backward is
`rectangular_cechVanishes`.  Gluing succeeds iff the constraint is
variable-separable — no coupling, no obstruction.

**The n-fold coupling.**  The generalized diagonal `allEqual n α` —
all `n` coordinates equal, over a finite alphabet `α` — is the maximal
coupling: every margin is full (`contextSections_allEqual`), so ALL
`|α|^n` families of local sections are compatible
(`compatibleFamilies_allEqual`, `compatibleFamilies_allEqual_encard`),
yet only the `|α|` constant vectors glue (`allEqual_encard`).  The
obstruction is therefore exactly `|α|^n - |α|`
(`cechObstruction_allEqual`), and for `|α| ≥ 2` it is at least
`2^n - 2` (`cechObstruction_allEqual_ge`): **exponential in the number
of variables**, while the feasible set itself keeps a constant `|α|`
points.  For `n ≥ 2` the constraint is genuinely non-rectangular
(`allEqual_not_rectangular`) and the obstruction is nonvanishing
(`allEqual_not_cechVanishes`), scaling `diagonal_not_rectangular` from
`Ste.Sheaf` to every arity.

**The dichotomy, honestly stated.**  `Ste.JunctionTree` proves the
easy side: at bounded induced width `w` over alphabets of size `≤ k`,
the junction-tree representation is faithful and of total size
`≤ n * k^(w+1)` — LINEAR in `n` for fixed width (Dechter 2003, bucket
elimination / junction trees).  `allEqual n α` sits at the opposite
extreme: its (primal) constraint graph is the complete graph — every
pair of variables interacts — so its width is maximal (`n - 1`), and
this file proves the price: the compatible/glued gap of the singleton
cover is `≥ 2^n - 2`.  Any procedure that reasons from the
per-variable margins alone must entertain exponentially many phantom
assignments that the coupling then kills.

**Honest boundary.**  What is mechanized is exactly: (i) the iff for
the SINGLETON cover on a product space, and (ii) the exact and
asymptotic obstruction counts for the `allEqual` family.  NOT claimed
or mechanized: that width `n - 1` is minimal for `allEqual` in the
formal `Ste.Treewidth` sense (the complete-graph width computation is
prose, not Lean); the general statement "every width-`w` bounded
representation of `allEqual` has size `≥ 2^n`" quantified over all
representation schemes; and the full cohomological `Ȟ¹` picture for
covers with nonempty overlaps (Abramsky–Brandenburger 2011), which
remains outlook.

References: R. Dechter, *Constraint Processing*, Morgan Kaufmann,
2003 (`dechter2003constraint`; bucket elimination, induced width,
junction trees); S. Abramsky, A. Brandenburger, *The sheaf-theoretic
structure of non-locality and contextuality*, New J. Phys. 13 (2011)
113036 (`abramsky2011sheaf`).
-/
import Mathlib.Data.Fintype.BigOperators
import Ste.CechObstruction

namespace STE

open Set

variable {V : Type*} {A : V → Type*}

/-! ### The singleton-cover characterization: gluing iff rectangular -/

/-- **The singleton-cover gluing characterization**: the Čech
obstruction of the singleton cover vanishes — every compatible family
of local sections glues to a global section — *iff* the constraint is
a rectangle `univ.pi P`.  This closes the singleton-cover half of the
presheaf gluing conjecture as a genuine iff: coupling is exactly the
obstruction to gluing. -/
theorem cechVanishes_iff_rectangular (T : Set (∀ v, A v)) :
    CechVanishes T ↔ ∃ P : ∀ v, Set (A v), T = Set.univ.pi P := by
  constructor
  · exact rectangular_of_cechVanishes
  · rintro ⟨P, rfl⟩
    exact rectangular_cechVanishes P

/-! ### The n-fold all-equal coupling -/

/-- The **n-fold all-equal constraint** (generalized diagonal): all
`n` coordinates carry the same value of the alphabet `α`.  This is the
maximal coupling — its (primal) constraint graph is complete, so its
induced width is `n - 1` — and it scales the two-variable `diagonal`
of `Ste.Sheaf` to arbitrary arity. -/
def allEqual (n : ℕ) (α : Type*) : Set (Fin n → α) :=
  {f | ∀ i j, f i = f j}

variable {n : ℕ} {α : Type*}

/-- Once there is at least one coordinate, the all-equal constraint is
exactly the range of the constant-vector embedding `a ↦ (fun _ ↦ a)`:
its global sections are the constant vectors. -/
theorem allEqual_eq_range (hn : 1 ≤ n) :
    allEqual n α = Set.range fun a : α => fun _ : Fin n => a := by
  ext f
  constructor
  · intro hf
    exact ⟨f ⟨0, hn⟩, funext fun j => hf ⟨0, hn⟩ j⟩
  · rintro ⟨a, rfl⟩
    exact fun _ _ => rfl

/-- **The feasible set stays small**: the all-equal constraint has
exactly `|α|` global sections — one constant vector per alphabet
value. -/
theorem allEqual_encard [Fintype α] (hn : 1 ≤ n) :
    (allEqual n α).encard = (Fintype.card α : ℕ∞) := by
  have hinj : Function.Injective fun a : α => fun _ : Fin n => a :=
    fun a b hab => congrFun hab ⟨0, hn⟩
  rw [allEqual_eq_range hn, ← Set.image_univ, hinj.encard_image,
    Set.encard_univ, ENat.card_eq_coe_fintype_card]

/-- Every margin of the all-equal constraint is full: any value at any
coordinate extends to the constant vector.  Locally the coupling is
invisible — all its information lives in the correlation. -/
theorem contextSections_allEqual (i : Fin n) :
    contextSections (allEqual n α) i = Set.univ :=
  Set.eq_univ_of_forall fun b => ⟨fun _ => b, fun _ _ => rfl, rfl⟩

/-- Since every margin is full, EVERY family of local sections is
compatible for the all-equal constraint: the compatible families are
the whole function space `Fin n → α`. -/
theorem compatibleFamilies_allEqual :
    compatibleFamilies (allEqual n α) = Set.univ := by
  refine Set.eq_univ_of_forall fun f => Set.mem_univ_pi.mpr fun i => ?_
  rw [contextSections_allEqual]
  exact Set.mem_univ _

/-- **The compatible count is exponential**: the all-equal constraint
admits `|α|^n` compatible families of local sections. -/
theorem compatibleFamilies_allEqual_encard [Fintype α] :
    (compatibleFamilies (allEqual n α)).encard
      = ((Fintype.card α ^ n : ℕ) : ℕ∞) := by
  rw [compatibleFamilies_allEqual, Set.encard_univ,
    ENat.card_eq_coe_fintype_card, Fintype.card_fun, Fintype.card_fin]

/-- **The exact obstruction of the n-fold coupling**:
`|α|^n` compatible families minus the `|α|` that glue.  Both counts
are finite, so the `ℕ∞` subtraction is the natural-number one,
cast. -/
theorem cechObstruction_allEqual [Fintype α] (hn : 1 ≤ n) :
    cechObstruction (allEqual n α)
      = ((Fintype.card α ^ n - Fintype.card α : ℕ) : ℕ∞) := by
  unfold cechObstruction
  rw [gluedFamilies_eq, compatibleFamilies_allEqual_encard,
    allEqual_encard hn, ← ENat.coe_sub]

/-! ### The exponential lower bound -/

/-- Monotonicity of `x ↦ x^n - x` in the base, at the point `2`: for
any alphabet size `k ≥ 2`, the gap `k^n - k` is at least the Boolean
gap `2^n - 2`.  (Truncated ℕ-subtraction; the key identity is
`k·(k^m − 1) = k^{1+m} − k`.) -/
theorem two_pow_sub_two_le {k : ℕ} (hk : 2 ≤ k) (hn : 1 ≤ n) :
    2 ^ n - 2 ≤ k ^ n - k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  calc 2 ^ (1 + m) - 2
      = 2 * (2 ^ m - 1) := by rw [Nat.mul_sub, mul_one, pow_add, pow_one]
    _ ≤ k * (k ^ m - 1) :=
        Nat.mul_le_mul hk (Nat.sub_le_sub_right (Nat.pow_le_pow_left hk m) 1)
    _ = k ^ (1 + m) - k := by rw [Nat.mul_sub, mul_one, pow_add, pow_one]

/-- **The exponential representation gap — the hard side of the
dichotomy.**  For any alphabet with at least two symbols, the Čech
obstruction of the n-fold all-equal coupling is at least `2^n - 2`:
exponentially many compatible families of local sections are stuck,
while the feasible set keeps only `|α|` points (`allEqual_encard`).

Contrast `Ste.JunctionTree.junctionTree_size_linear`: at bounded
induced width `w`, the faithful junction-tree representation has size
`≤ n * k^(w+1)` — linear in `n` (Dechter 2003).  `allEqual n α` has
the complete graph as its constraint graph (width `n - 1`, prose
observation), and here the margin-based picture provably overshoots
the feasible set by `≥ 2^n - 2`: unbounded coupling forces an
exponential gap that no per-variable (singleton-cover) account can
close. -/
theorem cechObstruction_allEqual_ge [Fintype α] (hn : 1 ≤ n)
    (hα : 2 ≤ Fintype.card α) :
    cechObstruction (allEqual n α) ≥ ((2 ^ n - 2 : ℕ) : ℕ∞) := by
  rw [cechObstruction_allEqual hn]
  exact ENat.coe_le_coe.mpr (two_pow_sub_two_le hα hn)

/-! ### Nonvanishing: the coupling is genuinely non-rectangular -/

/-- For `n ≥ 2` and at least two symbols, the all-equal constraint is
not a rectangle: a rectangle containing all constant vectors must
contain a mixed vector, which the coupling forbids.  This scales
`diagonal_not_rectangular` (`Ste.Sheaf`) to every arity. -/
theorem allEqual_not_rectangular [Fintype α] (hn : 2 ≤ n)
    (hα : 2 ≤ Fintype.card α) :
    ¬∃ P : Fin n → Set α, allEqual n α = Set.univ.pi P := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rintro ⟨P, hP⟩
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card hα
  -- every alphabet value sits in every side of the rectangle,
  -- via its constant vector
  have hconst : ∀ c : α, ∀ j, c ∈ P j := by
    intro c j
    have hc : (fun _ : Fin (m + 2) => c) ∈ allEqual (m + 2) α :=
      fun _ _ => rfl
    rw [hP] at hc
    exact Set.mem_univ_pi.mp hc j
  -- hence the mixed vector lies in the rectangle …
  have hmix : (fun j : Fin (m + 2) => if j = 0 then a else b)
      ∈ Set.univ.pi P := by
    refine Set.mem_univ_pi.mpr fun j => ?_
    by_cases hj : j = 0
    · rw [if_pos hj]; exact hconst a j
    · rw [if_neg hj]; exact hconst b j
  -- … so it would be all-equal, forcing `a = b`
  rw [← hP] at hmix
  have hne : (1 : Fin (m + 2)) ≠ 0 := Fin.ne_of_val_ne (by simp)
  have h01 : (if (0 : Fin (m + 2)) = 0 then a else b)
      = (if (1 : Fin (m + 2)) = 0 then a else b) := hmix 0 1
  rw [if_pos rfl, if_neg hne] at h01
  exact hab h01

/-- **Nonvanishing at every arity**: for `n ≥ 2` and at least two
symbols, the Čech obstruction of the n-fold coupling does not vanish —
some compatible family of local sections is stuck.  Immediate from the
characterization `cechVanishes_iff_rectangular` and
`allEqual_not_rectangular`. -/
theorem allEqual_not_cechVanishes [Fintype α] (hn : 2 ≤ n)
    (hα : 2 ≤ Fintype.card α) : ¬CechVanishes (allEqual n α) := fun h =>
  allEqual_not_rectangular hn hα
    ((cechVanishes_iff_rectangular _).mp h)

end STE
