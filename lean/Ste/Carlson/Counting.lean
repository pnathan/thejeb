/-
Carlson's cipher key-counting results.

Reference:
  A. H. Carlson, "Set Theoretic Estimation Applied to the Information
  Content of Ciphers and Decryption," Ph.D. dissertation, University of
  Idaho, May 2012, Chapter 4.

A substitution cipher over an alphabet `A` has a key that is a
*permutation* of `A` (`Equiv.Perm A`).  Given an intercepted message,
the only constraint the ciphertext places on the key is its action on
the set `T` of symbols that actually occur; any two keys that agree on
`T` decrypt the message identically — they are *equivalent* (Carlson,
Def. 2.3, "isomorphic keys").  Carlson's Lemma 4.1 counts them:

  **Lemma 4.1.** For a substitution cipher on message `M`, there are
  `(|A| - |T|)!` keys equivalent to the true key, where `T` is the set
  of distinct symbols in `M`.

We prove this as `card_consistent_keys`.  It is exactly the size of the
STE feasible key set after one observation, i.e. the residual key
ambiguity.
-/
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.End
import Mathlib.Logic.Equiv.Basic

namespace STE.Carlson

open Equiv

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The number of permutations of `A` fixing every element of a finset
`T` pointwise is `(|A| - |T|)!`: such a permutation is free on the
`|A| - |T|` symbols outside `T`. -/
theorem card_perm_fixing (T : Finset A) :
    Fintype.card {τ : Equiv.Perm A // ∀ a ∈ T, τ a = a}
      = (Fintype.card A - T.card)! := by
  classical
  have hcard : Fintype.card {a : A // a ∉ T} = Fintype.card A - T.card := by
    rw [Fintype.card_subtype_compl (fun a => a ∈ T)]
    congr 1
    exact Fintype.card_coe T
  -- Reindex the constraint into the shape of `subtypeEquivSubtypePerm`
  -- (permutations fixing the complement of a predicate pointwise).
  have e₁ : {τ : Equiv.Perm A // ∀ a ∈ T, τ a = a}
      ≃ {f : Equiv.Perm A // ∀ a, ¬(a ∉ T) → f a = a} :=
    Equiv.subtypeEquivRight (fun _ => by simp only [not_not])
  have e₂ : {f : Equiv.Perm A // ∀ a, ¬(a ∉ T) → f a = a}
      ≃ Equiv.Perm {a : A // a ∉ T} :=
    (Equiv.Perm.subtypeEquivSubtypePerm (p := fun a => a ∉ T)).symm
  calc Fintype.card {τ : Equiv.Perm A // ∀ a ∈ T, τ a = a}
      = Fintype.card (Equiv.Perm {a : A // a ∉ T}) :=
        Fintype.card_congr (e₁.trans e₂)
    _ = (Fintype.card {a : A // a ∉ T})! := Fintype.card_perm
    _ = (Fintype.card A - T.card)! := by rw [hcard]

/-- **Carlson, Lemma 4.1.**  For a substitution cipher with true key
`σ`, the keys equivalent to `σ` on a message whose symbol set is `T`
number `(|A| - |T|)!`.  Two keys are equivalent on the message exactly
when they agree on `T` (Carlson, Def. 2.3), so this counts the residual
key ambiguity — the size of the STE feasible key set after observing one
message. -/
theorem card_consistent_keys (σ : Equiv.Perm A) (T : Finset A) :
    Fintype.card {τ : Equiv.Perm A // ∀ a ∈ T, τ a = σ a}
      = (Fintype.card A - T.card)! := by
  rw [← card_perm_fixing T]
  -- Left-translation by `σ⁻¹` bijects keys agreeing with `σ` on `T`
  -- with keys fixing `T` pointwise.
  refine Fintype.card_congr
    { toFun := fun τ => ⟨σ⁻¹ * τ.1, fun a ha => ?_⟩
      invFun := fun ρ => ⟨σ * ρ.1, fun a ha => ?_⟩
      left_inv := fun τ => ?_
      right_inv := fun ρ => ?_ }
  · simp only [Equiv.Perm.mul_apply, τ.2 a ha]
    exact σ.symm_apply_apply a
  · simp only [Equiv.Perm.mul_apply, ρ.2 a ha]
  · apply Subtype.ext; simp only [mul_inv_cancel_left]
  · apply Subtype.ext; simp only [inv_mul_cancel_left]

/-- The number of keys of a substitution cipher on a block of symbols
`A` is `|A|!`: every key is a permutation of the block (Carlson Ch. 4;
here `Fintype.card (Perm A) = |A|!`). -/
theorem card_substitution_keys :
    Fintype.card (Equiv.Perm A) = (Fintype.card A)! :=
  Fintype.card_perm

end STE.Carlson
