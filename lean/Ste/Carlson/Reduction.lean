/-
Carlson's cipher-reduction results.

Reference:
  A. H. Carlson, "Set Theoretic Estimation Applied to the Information
  Content of Ciphers and Decryption," Ph.D. dissertation, University of
  Idaho, May 2012, Chapter 5.  See also A. Carlson et al., "Equivalence
  of Product Ciphers to Substitution Ciphers and their Security
  Implications," IEEE ISNCC 2022, and B. Ghosh et al., "Isomorphic
  Cipher Reduction," IEEE IEMCON 2021, which develop the same reduction.

We model the encoded-symbol space of a block as `B = Fin n → Bool`
(`n` bits).  A **substitution** cipher key is an arbitrary permutation of
`B` (`Equiv.Perm B`): every bijection on the value space is a
substitution key.  A **permutation** cipher key permutes the `n` bit
positions; a position permutation `ρ : Perm (Fin n)` induces the value
permutation `coperm ρ`.

Carlson's claims and their formal counterparts:
  * **Thm 5.2** — a permutation cipher reduces to a substitution cipher.
    Formally: `coperm` acts by relabelling coordinates
    (`coperm_apply : coperm ρ f x = f (ρ.symm x)`), it is a group
    homomorphism into the value-space symmetric group (`coperm_mul`,
    packaged as `copermHom`), and it is *injective*
    (`coperm_injective`).  The injective homomorphism is the content:
    permutation-cipher keys embed as a subgroup of the substitution-cipher
    keys (`permutation_reduces_to_substitution`).
  * **Lemma 5.1 / Cor 5.2** — a substitution cipher does not necessarily
    reduce to a permutation cipher: there are strictly more substitution
    keys than permutation keys on an `n`-bit block once `n ≥ 2`
    (`card_permutation_lt_card_substitution`), so no faithful embedding
    of permutation keys into substitution keys is onto
    (`substitution_not_reducible_to_permutation`).
  * **Cor 5.3** — a boundary-aligned PSP cipher is a single substitution
    cipher; every block cipher is a block substitution cipher.  Formally:
    the PSP composite acts by `s` conjugated with two independent
    coordinate relabellings (`psp_apply`), and the set of keys realized by
    the PSP construction is *exactly* the whole value-space symmetric
    group (`psp_reduces_to_substitution`) — closure and exhaustiveness at
    once.

Numbering note: the theorem/lemma numbers above follow the numbering of
the reduction chain in Chapter 5 of Carlson's dissertation as used
consistently throughout this project (Thm 5.2 for P → S, Lemma 5.1 /
Cor 5.2 for the failure of S → P, Cor 5.3 for PSP → S).  The copy of the
dissertation in `sources/` is a scanned PDF whose body text is not
machine-readable, so the numbers could not be re-verified mechanically;
they are used here only as attribution labels, and every statement below
stands on its own Lean proof.
-/
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Logic.Equiv.Basic

namespace STE.Carlson

/-- The value permutation induced by a bit-position permutation: relabel
the `n` coordinates of an `n`-bit value by `ρ`.  This realizes a
permutation-cipher key as a substitution-cipher key (a permutation of the
value space `Fin n → Bool`). -/
def coperm {n : ℕ} (ρ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n → Bool) :=
  ρ.arrowCongr (Equiv.refl Bool)

/-- **How a permutation key acts as a substitution key.**  `coperm ρ`
relabels the coordinates of an `n`-bit value: the bit that the input `f`
carries at position `ρ.symm x` is the bit the output carries at position
`x`.  This pins down the content of the reduction — a permutation cipher
*is* the substitution `f ↦ f ∘ ρ.symm` on the value space. -/
theorem coperm_apply {n : ℕ} (ρ : Equiv.Perm (Fin n)) (f : Fin n → Bool)
    (x : Fin n) : coperm ρ f x = f (ρ.symm x) := rfl

/-- `coperm` sends the identity position permutation to the identity
substitution key. -/
theorem coperm_one {n : ℕ} : coperm (1 : Equiv.Perm (Fin n)) = 1 := by
  ext f x
  rfl

/-- **`coperm` is a group homomorphism** (covariant: composing position
permutations composes the induced value permutations in the same order).
Together with `coperm_injective` this upgrades Carlson's Theorem 5.2 from
"each permutation key is some substitution key" to "the permutation keys
form a subgroup of the substitution keys". -/
theorem coperm_mul {n : ℕ} (ρ₁ ρ₂ : Equiv.Perm (Fin n)) :
    coperm (ρ₁ * ρ₂) = coperm ρ₁ * coperm ρ₂ := by
  ext f x
  rfl

/-- The realization of permutation-cipher keys as substitution-cipher
keys, packaged as a monoid (hence group) homomorphism from the position
symmetric group to the value symmetric group. -/
def copermHom {n : ℕ} : Equiv.Perm (Fin n) →* Equiv.Perm (Fin n → Bool) where
  toFun := coperm
  map_one' := coperm_one
  map_mul' := coperm_mul

/-- **Carlson, Theorem 5.2, sharpened.**  The realization `coperm` of
permutation-cipher keys as substitution-cipher keys is injective:
distinct bit-position permutations induce distinct value permutations.
`coperm ρ` acts by `f ↦ f ∘ ρ.symm` (`Equiv.arrowCongr` with the trivial
`Bool` component), so positions are separated by the `Bool` indicator of
a single coordinate.  Combined with
`card_permutation_lt_card_substitution`, this makes the embedding a
genuine non-surjective injection, so Lemma 5.1's non-reducibility is
concrete for `coperm`. -/
theorem coperm_injective {n : ℕ} : Function.Injective (coperm (n := n)) := by
  intro ρ₁ ρ₂ h
  have hsymm : ∀ x, ρ₁.symm x = ρ₂.symm x := by
    intro x
    have hx : (coperm ρ₁) (fun j => decide (j = ρ₁.symm x)) x
            = (coperm ρ₂) (fun j => decide (j = ρ₁.symm x)) x := by rw [h]
    have e1 : (coperm ρ₁) (fun j => decide (j = ρ₁.symm x)) x
            = decide (ρ₁.symm x = ρ₁.symm x) := rfl
    have e2 : (coperm ρ₂) (fun j => decide (j = ρ₁.symm x)) x
            = decide (ρ₂.symm x = ρ₁.symm x) := rfl
    rw [e1, e2] at hx
    have hx' : ρ₂.symm x = ρ₁.symm x := by simpa using hx.symm
    exact hx'.symm
  have hs : ρ₁.symm = ρ₂.symm := Equiv.ext hsymm
  calc ρ₁ = ρ₁.symm.symm := (ρ₁.symm_symm).symm
    _ = ρ₂.symm.symm := by rw [hs]
    _ = ρ₂ := ρ₂.symm_symm

/-- **Carlson, Theorem 5.2** (P reduces to S), stated with content.  The
permutation-cipher keys on an `n`-bit block embed into the
substitution-cipher keys: `copermHom` is an injective group homomorphism
`Perm (Fin n) →* Perm (Fin n → Bool)`, so the permutation keys form a
subgroup of the substitution keys, acting by `f ↦ f ∘ ρ.symm`
(`coperm_apply`).  Injectivity — not the mere existence of an image — is
the reduction's content. -/
theorem permutation_reduces_to_substitution {n : ℕ} :
    Function.Injective (copermHom (n := n)) :=
  coperm_injective

/-- On an `n`-bit block with `2 ≤ n`, there are strictly more
substitution-cipher keys (`(2^n)!` permutations of the value space) than
permutation-cipher keys could ever be (`n!` permutations of the bit
positions).  This is the quantitative heart of Carlson's Lemma 5.1 /
Corollary 5.2. -/
theorem card_permutation_lt_card_substitution {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card (Equiv.Perm (Fin n))
      < Fintype.card (Equiv.Perm (Fin n → Bool)) := by
  rw [Fintype.card_perm, Fintype.card_perm, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]
  exact Nat.factorial_lt_of_lt (by omega) (Nat.lt_two_pow_self)

/-- **Carlson, Lemma 5.1 / Corollary 5.2** (S does not reduce to P).
For `2 ≤ n`, no injective realization of permutation-cipher keys as
substitution-cipher keys on an `n`-bit block is surjective: some
substitution cipher is not a permutation cipher.  Quantified over every
faithful embedding `ι`, so it does not depend on a particular
construction. -/
theorem substitution_not_reducible_to_permutation {n : ℕ} (hn : 2 ≤ n)
    (ι : Equiv.Perm (Fin n) → Equiv.Perm (Fin n → Bool))
    (hinj : Function.Injective ι) : ¬ Function.Surjective ι := by
  intro hsurj
  have h := Fintype.card_of_bijective ⟨hinj, hsurj⟩
  exact absurd h (Nat.ne_of_lt (card_permutation_lt_card_substitution hn))

/-- The set of substitution keys realized by the
permutation–substitution–permutation construction with two *independent*
position permutations. -/
def pspKeys (n : ℕ) : Set (Equiv.Perm (Fin n → Bool)) :=
  {t | ∃ (ρ₁ ρ₂ : Equiv.Perm (Fin n)) (s : Equiv.Perm (Fin n → Bool)),
        coperm ρ₁ * s * coperm ρ₂ = t}

/-- **How a PSP key acts.**  The composite
`coperm ρ₁ * s * coperm ρ₂` first relabels the input coordinates by `ρ₂`,
then applies the substitution `s`, then reads off the result at the
coordinate relabelled by `ρ₁`.  Explicitly computing the action is what
makes the closure statement below non-vacuous. -/
theorem psp_apply {n : ℕ} (ρ₁ ρ₂ : Equiv.Perm (Fin n))
    (s : Equiv.Perm (Fin n → Bool)) (f : Fin n → Bool) (x : Fin n) :
    (coperm ρ₁ * s * coperm ρ₂) f x = s (fun y => f (ρ₂.symm y)) (ρ₁.symm x) :=
  rfl

/-- **Carlson, Corollary 5.3** (PSP reduces to S; every block cipher is a
block substitution cipher).  The keys realized by the
permutation–substitution–permutation construction with two independent
position permutations are *exactly* the substitution keys: `pspKeys n` is
all of `Perm (Fin n → Bool)`.  The `⊆` direction is closure — a PSP
cipher is a single substitution cipher, acting as in `psp_apply`; the `⊇`
direction (take `ρ₁ = ρ₂ = 1`) says the construction gains nothing, so
the reduction is an equality of key spaces, not just an inclusion. -/
theorem psp_reduces_to_substitution {n : ℕ} : pspKeys n = Set.univ := by
  ext t
  simp only [pspKeys, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact ⟨1, 1, t, by simp [coperm_one]⟩

end STE.Carlson
