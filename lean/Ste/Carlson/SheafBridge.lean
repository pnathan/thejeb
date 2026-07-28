/-
Bridging Carlson's cipher STE results to the project's sheaf/support
layer.

Reference:
  A. H. Carlson, "Set Theoretic Estimation Applied to the Information
  Content of Ciphers and Decryption," Ph.D. dissertation, University of
  Idaho, May 2012 (advisors R. E. Hiromoto and R. B. Wells).

`Ste.Carlson.Cipher` recasts decryption as an STE problem on the key
space; `Ste.Carlson.Counting` computes the residual key ambiguity
(Carlson, Lemma 4.1); `Ste.Support` and `Ste.VariablePresheaf` develop
the *scope* (support) of a constraint and the variable-side presheaf of
local sections independently of ciphers.  This file connects the two
developments — the "Carlson dissertation connection points" of
`papers/papers/ste-cohomology.tex`:

* **Scoped decryption constraint.**  The set of decryption maps under
  which a ciphertext `c` reads meaningfully depends only on the symbols
  occurring in `c` (`hasSupport_decConstraint`) — decryption constraints
  are exactly the kind of scoped (finitely-supported) constraint
  `Ste.Support` studies.
* **The substitution cipher.**  `subCipher` instantiates Carlson's
  `CipherSystem` for substitution ciphers (keys = alphabet permutations),
  and `mem_keyPropertySet_iff_decConstraint` identifies Carlson's
  `keyPropertySet` (the STE property set on keys) with `decConstraint`
  read through the inverse key.
* **Non-rectangularity of the key coupling.**  The bijective-map
  constraint on the key space is not a product constraint
  (`bijKeys_not_rectangular`): a single ciphertext observation couples
  the key's values at different symbols, the same obstruction shape as
  `Ste.Sheaf.diagonal_not_rectangular`.
* **Residual keys as a fiber of the sections functor.**  Carlson's
  Lemma 4.1 residual-key count (`card_consistent_keys`) is exactly the
  cardinality of the fiber of the restriction map used to define
  `Ste.VariablePresheaf.localSections` (`card_restrict_fiber`): the
  "keys agreeing with the true key on the observed symbols" are the
  keys restricting to the same local section.
-/
import Mathlib.Data.List.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Ste.Carlson.Cipher
import Ste.Carlson.Counting
import Ste.Support
import Ste.VariablePresheaf
import Ste.RepresentationBounds

namespace STE.Carlson

open Set Nat

variable {A : Type*}

/-! ### 1. The decryption-side constraint is scoped -/

/-- **Carlson's per-ciphertext decryption constraint.**  The set of
decryption maps `d : A → A` under which the ciphertext `c` decodes to a
meaningful message (`c.map d ∈ Meaning`).  This is the same data as
`CipherSystem.keyPropertySet` for the substitution cipher, phrased
directly on decryption maps rather than on `Equiv.Perm`
(`mem_keyPropertySet_iff_decConstraint` below relates the two). -/
def decConstraint (Meaning : Set (List A)) (c : List A) : Set (A → A) :=
  {d | c.map d ∈ Meaning}

/-- **The decryption constraint is scoped to the observed symbols**
(Carlson 2012, the STE recast: a ciphertext only ever constrains the key
on the symbols it contains).  Membership of `d` in `decConstraint Meaning
c` depends only on the values of `d` on the symbols occurring in `c`,
since `c.map d` only ever evaluates `d` there.  Discharges the "Carlson
connection" scoped-observation claim of `papers/papers/ste-cohomology.tex`. -/
theorem hasSupport_decConstraint (Meaning : Set (List A)) (c : List A) :
    HasSupport (decConstraint Meaning c) {a : A | a ∈ c} := by
  intro f g hfg
  have heq : c.map f = c.map g := List.map_congr_left hfg
  simp only [decConstraint, Set.mem_setOf_eq, heq]

/-! ### 2. The bridge to Carlson's `keyPropertySet` -/

/-- **The substitution cipher.**  Keys are alphabet permutations,
messages and ciphertexts are lists over the alphabet, and encryption
applies the key symbol-wise.  Injectivity of `List.map` of an injective
function makes this a genuine `CipherSystem` (Carlson 2012, Ch. 2-4). -/
def subCipher (A : Type*) : CipherSystem (Equiv.Perm A) (List A) (List A) where
  enc τ m := m.map (⇑τ)
  enc_injective τ := List.map_injective_iff.mpr τ.injective

/-- **`keyPropertySet` is `decConstraint` read through the inverse key**
(Carlson 2012, the STE recast of decryption: a key `τ` decrypts `c` to a
meaningful message iff applying its inverse to `c` symbol-wise lands in
`Meaning`).  Discharges the "Carlson connection" bridge claim of
`papers/papers/ste-cohomology.tex`. -/
theorem mem_keyPropertySet_iff_decConstraint (Meaning : Set (List A))
    (c : List A) (τ : Equiv.Perm A) :
    τ ∈ (subCipher A).keyPropertySet Meaning c ↔
      (⇑τ⁻¹ : A → A) ∈ decConstraint Meaning c := by
  simp only [CipherSystem.keyPropertySet, Set.mem_setOf_eq, subCipher,
    decConstraint]
  constructor
  · rintro ⟨m, hm, hmc⟩
    have hmap : c.map (⇑τ⁻¹) = m := by
      rw [← hmc, List.map_map]
      simp
    rw [hmap]; exact hm
  · intro h
    refine ⟨c.map (⇑τ⁻¹), h, ?_⟩
    rw [List.map_map]
    simp

/-! ### 3. The permutation coupling is not rectangular -/

/-- **The bijective-key constraint on the alphabet-indexed product
space.**  A decryption map is a genuine key exactly when it is
bijective; this is the constraint whose restrictions to symbol sets
Carlson's counting (§4) tracks. -/
def bijKeys (A : Type*) : Set (A → A) := {g | Function.Bijective g}

/-- **The permutation coupling is not rectangular.**  A single
ciphertext observation constrains the key jointly across the symbols it
contains: `bijKeys A` is not a product constraint `∏ₐ Pₐ`.  Proof
mimics `Ste.Sheaf.diagonal_not_rectangular`: if it were a product, the
identity key witnesses `a ∈ P a` for every `a`, and the transposition of
two distinct symbols `a ≠ b` witnesses `b ∈ P a`; mixing these two
witnesses coordinatewise at `a` alone produces a map sending both `a`
and `b` to `b`, which lies in the would-be product but is not
injective — contradiction.  This is the same coupling obstruction shape
underlying `Ste.Sheaf.diagonal_not_rectangular`, instantiated at
Carlson's key space. -/
theorem bijKeys_not_rectangular [Nontrivial A] : ¬ IsRectangle (bijKeys A) := by
  classical
  rintro ⟨P, hP⟩
  obtain ⟨a, b, hab⟩ := exists_pair_ne A
  have hid : (id : A → A) ∈ Set.univ.pi P := by
    rw [← hP]
    exact Function.bijective_id
  have hswap : (⇑(Equiv.swap a b) : A → A) ∈ Set.univ.pi P := by
    rw [← hP]
    exact (Equiv.swap a b).bijective
  have hidP : ∀ x, x ∈ P x := fun x => by
    simpa using Set.mem_univ_pi.mp hid x
  have hswapP : (Equiv.swap a b) a ∈ P a := Set.mem_univ_pi.mp hswap a
  have hbP : b ∈ P a := by rwa [Equiv.swap_apply_left] at hswapP
  set g : A → A := Function.update (id : A → A) a b with hg
  have hgmem : g ∈ Set.univ.pi P := by
    rw [Set.mem_univ_pi]
    intro x
    by_cases hx : x = a
    · subst hx
      simpa [hg, Function.update_self] using hbP
    · simpa [hg, Function.update_of_ne hx] using hidP x
  have hgbij : Function.Bijective g := show g ∈ bijKeys A by rw [hP]; exact hgmem
  have hga : g a = b := by rw [hg]; exact Function.update_self a b id
  have hgb : g b = b := by rw [hg]; exact Function.update_of_ne (Ne.symm hab) b id
  exact hab (hgbij.1 (hga.trans hgb.symm))

/-! ### 4. Residual keys are the fiber of a local section -/

/-- **Carlson's residual-key count is a fiber of the sections-functor
restriction map** (Carlson 2012, Lemma 4.1, read through
`Ste.VariablePresheaf.localSections`).  The permutations restricting to
the same partial assignment as `σ` on the finite symbol set `T` — i.e.
lying in the same fiber of `(↑T : Set A).restrict` as `σ` — number
`(|A| - |T|)!`, exactly Carlson's residual key ambiguity after one
observation whose distinct symbols are `T`. -/
theorem card_restrict_fiber [Fintype A] [DecidableEq A] (σ : Equiv.Perm A)
    (T : Finset A) :
    Fintype.card
        {τ : Equiv.Perm A // (↑T : Set A).restrict (⇑τ) =
          (↑T : Set A).restrict (⇑σ)} =
      (Fintype.card A - T.card)! := by
  rw [← card_consistent_keys σ T]
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun τ => ?_)
  constructor
  · intro h a ha
    have := congrFun h ⟨a, ha⟩
    simpa [Set.restrict] using this
  · intro h
    funext x
    obtain ⟨a, ha⟩ := x
    simpa [Set.restrict] using h a ha

end STE.Carlson
