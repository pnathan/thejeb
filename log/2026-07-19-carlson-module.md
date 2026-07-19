# 2026-07-19 — Carlson cipher module: counting and reduction

This session built out Carlson's Chapter 4 (key counting) and Chapter 5
(cipher reduction) results as a dedicated, CI-checked submodule, and
sharpened Theorem 5.2 into an injective embedding.

## Module restructure

The previous single `Ste.Cipher` file (STE-decryption skeleton) was moved
into a `STE.Carlson` namespace and split into a directory:

- `lean/Ste/Carlson/Cipher.lean` — the STE-decryption skeleton
  (`CipherSystem`, `keyPropertySet`, `feasibleKeys`, `fair_of_genuine`,
  `feasibleKeys_nonempty_of_genuine`, `Unicity.eq_of_feasible`,
  `feasibleKeys_antitone`). Identifiers formerly `CipherSystem.*` /
  `Unicity.*` are now under `STE.Carlson.CipherSystem.*`.
- `lean/Ste/Carlson/Counting.lean` — Lemma 4.1 (new).
- `lean/Ste/Carlson/Reduction.lean` — Theorem 5.2 / Lemma 5.1 /
  Corollary 5.3 (new).
- `lean/Ste/Carlson.lean` — aggregator importing the three.
- `lean/Ste.lean` — edited to import the Carlson aggregator.

## Theorems proven (all CI-green)

Counting (`Ste.Carlson.Counting`):
- `STE.Carlson.card_perm_fixing (T : Finset A)` :
  `#{τ : Perm A // ∀ a ∈ T, τ a = a} = (|A| - |T|)!`. Reindexes the
  fixing constraint to `Equiv.Perm {a // a ∉ T}` via
  `Equiv.subtypeEquivRight` and `Equiv.Perm.subtypeEquivSubtypePerm`,
  then `Fintype.card_perm`; the outside-`T` count comes from
  `Fintype.card_subtype_compl` and `Fintype.card_coe`.
- `STE.Carlson.card_consistent_keys (σ : Perm A) (T : Finset A)` :
  `#{τ : Perm A // ∀ a ∈ T, τ a = σ a} = (|A| - |T|)!` — **Carlson
  Lemma 4.1**. Proved by a hand-built `Equiv` (left-translation by
  `σ⁻¹`) bijecting keys agreeing with `σ` on `T` with keys fixing `T`
  pointwise, then `card_perm_fixing`.
- `STE.Carlson.card_substitution_keys` : `#(Perm A) = |A|!`.

Reduction (`Ste.Carlson.Reduction`):
- `coperm (ρ : Perm (Fin n)) : Perm (Fin n → Bool)` :=
  `ρ.arrowCongr (Equiv.refl Bool)`, acting by `coperm ρ f x = f (ρ⁻¹ x)`.
- `STE.Carlson.permutation_reduces_to_substitution` — **Thm 5.2** (P ⊆ S).
- `STE.Carlson.coperm_injective : Function.Injective coperm` — **new**;
  upgrades Thm 5.2 to a genuine injective embedding (see below).
- `STE.Carlson.card_permutation_lt_card_substitution (hn : 2 ≤ n)` :
  `#(Perm (Fin n)) < #(Perm (Fin n → Bool))`, i.e. `n! < (2^n)!` — via
  `Fintype.card_perm`, `Fintype.card_fun`, `Nat.factorial_lt_of_lt`,
  `Nat.lt_two_pow_self`.
- `STE.Carlson.substitution_not_reducible_to_permutation` — **Lemma 5.1
  / Cor 5.2**: no injective realization of permutation keys as
  substitution keys is surjective (quantified over every embedding).
- `STE.Carlson.psp_reduces_to_substitution` — **Cor 5.3**: every PSP
  composition is a single substitution cipher.

## CI failures hit and fixes

1. **Factorial `!` parse error (the failing HEAD at session start).**
   `Counting.lean` used the `(n)!` factorial notation in three theorem
   statements but did not import its definition, and the notation is
   `scoped` to the `Nat` namespace. Error:
   `unexpected token '!'; expected ':=', 'where' or '|'` at the three
   statement lines. Confirmed against the Mathlib v4.32.0 clone that
   `scoped notation:10000 n "!" => Nat.factorial n` lives in
   `Mathlib/Data/Nat/Factorial/Basic.lean` inside `namespace Nat`.
   **Fix:** added `import Mathlib.Data.Nat.Factorial.Basic` and changed
   `open Equiv` to `open Equiv Nat`. (Reduction.lean was unaffected
   because it used the fully-qualified `Nat.factorial_lt_of_lt`, never
   the notation.) Commit `bc143fd` → CI green.

2. **No other Lean failures.** The `card_consistent_keys` hand-built
   `Equiv` (untested at session start) compiled on the first green run.

## coperm_injective — landed

Proven on the first CI attempt (commit `9f3d575`, green). Method: for a
fixed `x`, evaluate `coperm ρ` on the `Bool` indicator
`fun j => decide (j = ρ₁.symm x)`; since `coperm ρ g x = g (ρ.symm x)`
(definitional, from `arrowCongr`), equality of the two induced
permutations forces `ρ₁.symm x = ρ₂.symm x` for all `x`, hence
`ρ₁.symm = ρ₂.symm` (`Equiv.ext`) and `ρ₁ = ρ₂` (`Equiv.symm_symm`).
Note: `Equiv.symm_injective` does not exist in this Mathlib; the
`symm_symm` round-trip was used instead. The two evaluation steps are
closed by `rfl` (definitional unfolding of `arrowCongr` + `Equiv.refl`).

## Verification

- `bc143fd` (Counting import fix) — run #6, green.
- `9f3d575` (coperm_injective) — run #7, green: `Build the Ste library`
  succeeded. This is the machine-checked state for Lemma 4.1 and the
  full reduction chain.

Papers/logs updated in a follow-up commit:
`papers/papers/ste-mechanization.tex` (new counting + reduction
sections, namespace fixes), `papers/notes/literature-review.tex`
(Carlson "what we formalized" now lists Lemma 4.1 and the 5.2/5.1/5.3
chain as proven), and `log/2026-07-19-hypotheses-ste-core.md` (H9, H10
marked PROVEN).
