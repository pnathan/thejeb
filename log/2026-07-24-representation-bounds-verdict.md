# 2026-07-24 — Verdict: "obstruction size = representation blow-up" is FALSE (complexity reading); the correct statement is a sandwich of bounds

Branch: `research/representation-bounds`.
New module: `lean/Ste/RepresentationBounds.lean` (imported from `lean/Ste.lean`), sorry/axiom/native_decide-free.
Companion note: `papers/notes/representation-bounds-litreview.tex` (+ PDF, pdflatex×2 + bibtex, 0 errors, 0 undefined citations; 5 new grounded BibTeX entries appended to `refs.bib`, plus a fix of a pre-existing missing `}` in `seidel1981invasion` that was silently corrupting the following entry).

## The verdict

The open item asked whether `cechObstruction T` (count of compatible-but-stuck
families for the singleton cover, `Ste.CechObstruction`) EQUALS the forced
representation blow-up of `T`. Answer: **the equality is false as a theorem
about representations; it survives only as a definition.** Two readings:

1. **Box-gap reading — `=` holds, tautologically.** The smallest single
   rectangle containing `T` is the box `∏ᵥ projᵥ(T) = compatibleFamilies T`,
   and `cechObstruction T = |compatibleFamilies T| − |T|` by unfolding.
   Mechanized as `cechObstruction_eq_box_sub_encard` + `compatibleFamilies_eq_boxProduct`.
   This is bookkeeping, not a representation theorem.

2. **Rectangle-cover-complexity reading (the real one) — `=`, `≤`, `≥` ALL
   fail uniformly.** With `ρ(T) := rectCoverNumber T` = least number of
   rectangles whose union is exactly `T` (the nondeterministic cover number
   `C¹` of Kushilevitz–Nisan 1997, read on `T` as a tensor):
   - **no uniform `obstruction ≤ ρ`**: `allEqual n α` with `n ≥ 3`, `k = |α| ≥ 2`
     has `ρ = k < kⁿ − k = obstruction` (witness `allEqual 3 Bool`: `2 < 6`);
   - **no uniform `ρ ≤ obstruction`**: any nonempty rectangle has
     `obstruction = 0 < 1 = ρ` (witness `univ` on one Boolean variable);
   - both refutations are machine-checked
     (`not_forall_cechObstruction_le_rectCoverNumber`,
     `not_forall_rectCoverNumber_le_cechObstruction`).
   - **the likely origin of the conjecture**: at the minimal nonvanishing
     instance, the 2×2 Boolean `diagonal` (= `allEqual 2 Bool`,
     `diagonal_eq_allEqual`), the two invariants COINCIDE: obstruction
     `= 2 = ρ` (`diagonal_cechObstruction_eq_rectCoverNumber`). A coincidence
     of the smallest example, not a law: broken already at `n = 3`.

   **What is true instead (all mechanized):** the fooling sandwich
   `foolingNumber T ≤ ρ(T) ≤ |T|`, the boundary agreement
   `ρ(T) = 1 ⟺ T nonempty rectangle ⟺ Čech obstruction vanishes`
   (hence `ρ ≥ 2 ⟺ obstruction nonvanishing`, for nonempty `T`), and the
   exact coupling value `ρ(allEqual n α) = |α|` (`n ≥ 2`) via the
   constant-vector fooling set — while the obstruction of the same constraint
   is `|α|ⁿ − |α|`. Obstruction is a *volume* invariant; ρ is a *covering*
   invariant. They agree in vanishing behavior at the bottom of the scale and
   nowhere else uniformly.

## What closed in Lean (verbatim statements, all sorry-free)

Definitions: `IsRectangle`, `HasRectCover`, `rectCoverNumber`,
`IsFoolingSet`, `foolingNumber` (namespace `STE`, in
`Ste/RepresentationBounds.lean`).

```lean
theorem IsFoolingSet.encard_le_of_hasRectCover {T F : Set (∀ v, A v)}
    (hF : IsFoolingSet T F) {m : ℕ} (hm : HasRectCover T m) :
    F.encard ≤ (m : ℕ∞)

theorem foolingNumber_le_rectCoverNumber (T : Set (∀ v, A v)) :
    foolingNumber T ≤ rectCoverNumber T

theorem rectCoverNumber_le_encard (T : Set (∀ v, A v)) :
    rectCoverNumber T ≤ T.encard

theorem rectCoverNumber_eq_one_iff {T : Set (∀ v, A v)} :
    rectCoverNumber T = 1 ↔ T.Nonempty ∧ IsRectangle T

theorem rectCoverNumber_eq_one_iff_cechVanishes {T : Set (∀ v, A v)}
    (hT : T.Nonempty) : rectCoverNumber T = 1 ↔ CechVanishes T

theorem one_lt_rectCoverNumber_iff {T : Set (∀ v, A v)}
    (hT : T.Nonempty) : 1 < rectCoverNumber T ↔ ¬CechVanishes T

theorem compatibleFamilies_eq_boxProduct (T : Set (∀ v, A v)) :
    compatibleFamilies T = Set.univ.pi fun v => (fun f => f v) '' T

theorem cechObstruction_eq_box_sub_encard (T : Set (∀ v, A v)) :
    cechObstruction T = (compatibleFamilies T).encard - T.encard

theorem isFoolingSet_allEqual {n : ℕ} {α : Type*} (hn : 2 ≤ n) :
    IsFoolingSet (allEqual n α) (allEqual n α)

theorem rectCoverNumber_allEqual {n : ℕ} {α : Type*} [Fintype α]
    (hn : 2 ≤ n) :
    rectCoverNumber (allEqual n α) = (Fintype.card α : ℕ∞)

theorem foolingNumber_allEqual {n : ℕ} {α : Type*} [Fintype α]
    (hn : 2 ≤ n) :
    foolingNumber (allEqual n α) = (Fintype.card α : ℕ∞)

theorem rectCoverNumber_lt_cechObstruction_allEqual {n : ℕ} {α : Type*}
    [Fintype α] (hn : 3 ≤ n) (hα : 2 ≤ Fintype.card α) :
    rectCoverNumber (allEqual n α) < cechObstruction (allEqual n α)

theorem exists_rectCoverNumber_lt_cechObstruction :
    ∃ (V : Type) (A : V → Type) (T : Set (∀ v, A v)),
      rectCoverNumber T < cechObstruction T

theorem exists_cechObstruction_lt_rectCoverNumber :
    ∃ (V : Type) (A : V → Type) (T : Set (∀ v, A v)),
      cechObstruction T < rectCoverNumber T

theorem not_forall_rectCoverNumber_le_cechObstruction :
    ¬ ∀ (V : Type) (A : V → Type) (T : Set (∀ v, A v)),
        rectCoverNumber T ≤ cechObstruction T

theorem not_forall_cechObstruction_le_rectCoverNumber :
    ¬ ∀ (V : Type) (A : V → Type) (T : Set (∀ v, A v)),
        cechObstruction T ≤ rectCoverNumber T

theorem diagonal_eq_allEqual : diagonal = allEqual 2 Bool

theorem rectCoverNumber_diagonal : rectCoverNumber diagonal = 2

theorem diagonal_cechObstruction_eq_rectCoverNumber :
    cechObstruction diagonal = rectCoverNumber diagonal
```

Supporting lemmas also closed: `isRectangle_univ`, `isRectangle_singleton`,
`IsRectangle.mix_mem` (rectangles closed under coordinatewise mixing — the
fooling-set engine), `hasRectCover_zero_iff`, `rectCoverNumber_le`,
`le_rectCoverNumber`, `exists_rectCoverNumber_eq` (the infimum is attained),
`exists_hasRectCover_of_ne_top`, `rectCoverNumber_eq_zero_iff`,
`one_le_rectCoverNumber`, `IsFoolingSet.le_foolingNumber`.

## What did NOT close (honest boundary — none attempted-and-failed; these are scoped out)

- The log-scale relation `log₂ ρ = nondeterministic communication
  complexity ± O(1)` (Kushilevitz–Nisan): not formalized; the STE obstruction
  is counted on the linear scale, and the protocol model is not in the repo.
- Nonnegative rank / extension complexity refinements (Yannakakis 1991,
  Fiorini et al. 2015): cited as context only.
- Cover-relative `ρ` for covers with nonempty overlaps (`Ste.CechCover`):
  open, see conjectures.
- The partition (disjoint-cover) number `ρ^⊔`: not defined in Lean yet.

## New conjectures for the queue

1. **Additive reconciliation**: for finite nonempty non-rectangular `T`, is
   `ρ(T) ≤ cechObstruction T + 1`? (True on all computed instances:
   `allEqual` gives `k ≤ kⁿ−k+1` for `n,k ≥ 2`; rectangles are excluded by
   hypothesis. The fooling bound does not obstruct it. Candidate mechanization
   target; a counterexample would need many rectangles but tiny box gap —
   e.g. try near-diagonal unions of overlapping rectangles.)
2. **Partition number of the coupling**: `ρ^⊔(allEqual n α) = |α|` — the
   constant-singleton partition gives `≤`, the same fooling set gives `≥`;
   should mechanize with the existing machinery almost verbatim.
3. **Graded/cover-relative comparison**: define `ρ` relative to a variable
   cover `U : J → Set V` (rectangles replaced by `U`-local products) and ask
   whether `ρ_U = 1` matches `CechVanishesCover U` of `Ste.CechCover`.

Rule observed: distrust results that aren't machine proven — every claim
above marked "mechanized" compiles in CI on this branch; everything else is
attributed to the literature or explicitly listed as open.
