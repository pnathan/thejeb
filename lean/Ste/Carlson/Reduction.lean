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
  * **Thm 5.2** — a permutation cipher reduces to a substitution cipher:
    `coperm ρ` is a permutation of the value space, i.e. a substitution
    key (`permutation_reduces_to_substitution`).
  * **Lemma 5.1 / Cor 5.2** — a substitution cipher does not necessarily
    reduce to a permutation cipher: there are strictly more substitution
    keys than permutation keys on an `n`-bit block once `n ≥ 2`
    (`card_permutation_lt_card_substitution`), so no faithful embedding
    of permutation keys into substitution keys is onto
    (`substitution_not_reducible_to_permutation`).
  * **Cor 5.3** — a boundary-aligned PSP cipher is a single substitution
    cipher; every block cipher is a block substitution cipher, because
    the value-space symmetric group is closed under composition
    (`psp_reduces_to_substitution`).
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

/-- **Carlson, Theorem 5.2** (P reduces to S).  Every permutation-cipher
key is a substitution-cipher key: `coperm ρ` is a permutation of the
value space. -/
theorem permutation_reduces_to_substitution {n : ℕ} (ρ : Equiv.Perm (Fin n)) :
    ∃ s : Equiv.Perm (Fin n → Bool), s = coperm ρ :=
  ⟨coperm ρ, rfl⟩

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

/-- **Carlson, Corollary 5.3** (PSP reduces to S; every block cipher is a
block substitution cipher).  A permutation–substitution–permutation
composition is again a single permutation of the value space, hence a
substitution key: the value-space symmetric group is closed under
composition. -/
theorem psp_reduces_to_substitution {n : ℕ} (ρ : Equiv.Perm (Fin n))
    (s : Equiv.Perm (Fin n → Bool)) :
    ∃ t : Equiv.Perm (Fin n → Bool), coperm ρ * s * coperm ρ = t :=
  ⟨_, rfl⟩

end STE.Carlson
