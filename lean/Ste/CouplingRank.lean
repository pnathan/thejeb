/-
Coupling dichotomy for the partition-lattice rank.

`Ste.PartitionRank` equips the partition lattice `Setoid α` of a finite
carrier with the combinatorial (metric-free) rank `r(P) = |α| − #blocks(P)`
and shows it is submodular, the shadow of Shannon entropy submodularity in
his 1953 information lattice.  Its closing remark ("Coupling and rank: a
conjecture") asks for a precise statement of the intuition that a reading
which is *decomposable* relative to a grouping should not lose rank when
read against that grouping, while a reading that genuinely *couples*
information across the grouping's blocks should.

This module proves exactly that dichotomy at the combinatorial-rank level,
closing the open conjecture at this layer (short of the hypothesis-space
entropy layer the note also gestures at, which remains future work).  For a
reading `P` and a grouping `Γ`, both elements of the `Setoid α` refinement
lattice:

* if `P ≤ Γ` (every `P`-block sits inside one `Γ`-block — `P` is
  decomposable relative to `Γ`), meeting with `Γ` is a no-op on rank
  (`rank_inf_eq_of_le`);
* if `P ≰ Γ` (`P` couples information across `Γ`'s blocks), meeting with
  `Γ` strictly lowers rank (`rank_inf_lt_of_not_le`).

The two cases are exhaustive and mutually exclusive (`rank_inf_eq_iff`), and
the gap between them, `couplingExcess P Γ = rank P − rank (P ⊓ Γ)`, is the
finite, metric-free analogue of a multi-group total-correlation / mutual-
information term: nonnegative always, zero exactly on decomposable readings,
strictly positive exactly on coupled ones.
-/
import Ste.PartitionRank

namespace STE

open STE.PartitionRank

variable {α : Type*} [Fintype α] (P Γ : Setoid α)

noncomputable section

open scoped Classical

/-- Meeting a reading `P` with any grouping `Γ` can only lose rank. -/
theorem rank_inf_le_left : rank (P ⊓ Γ) ≤ rank P :=
  rank_le_rank inf_le_left

/-- The DECOMPOSABLE case: if `P` already refines `Γ` (every `P`-block sits
inside a single `Γ`-block), meeting with `Γ` leaves the rank unchanged. -/
theorem rank_inf_eq_of_le (h : P ≤ Γ) : rank (P ⊓ Γ) = rank P := by
  rw [inf_eq_left.mpr h]

/-- The COUPLING case: if `P` does *not* refine `Γ`, some pair of elements
that `P` identifies is split apart by `Γ`, so meeting `P` with `Γ` strictly
drops the rank — `P` genuinely couples information across `Γ`'s blocks. -/
theorem rank_inf_lt_of_not_le (h : ¬ P ≤ Γ) : rank (P ⊓ Γ) < rank P := by
  have hex : ∃ u v, P u v ∧ ¬ Γ u v := by
    by_contra hcon
    push_neg at hcon
    exact h (fun {u v} huv => hcon u v huv)
  obtain ⟨u, v, hPuv, hΓuv⟩ := hex
  have hnot : ¬ (P ⊓ Γ) u v := fun huv => hΓuv huv.2
  have hlt : blockCount P < blockCount (P ⊓ Γ) :=
    blockCount_lt inf_le_left hnot hPuv
  have hle : blockCount (P ⊓ Γ) ≤ Fintype.card α := blockCount_le_card _
  simp only [rank]
  omega

/-- The dichotomy, as an `iff`: meeting `P` with `Γ` preserves rank exactly
when `P` is decomposable relative to `Γ`. Combines `rank_inf_eq_of_le` and
`rank_inf_lt_of_not_le`. -/
theorem rank_inf_eq_iff : rank (P ⊓ Γ) = rank P ↔ P ≤ Γ := by
  constructor
  · intro heq
    by_contra hnle
    have hlt := rank_inf_lt_of_not_le P Γ hnle
    omega
  · exact rank_inf_eq_of_le P Γ

/-- The finite, metric-free analogue of a multi-group total-correlation /
mutual-information term: how much rank (forced-identification information)
the reading `P` loses when read against the grouping `Γ`.  It is `≥ 0`
always (`rank_inf_le_left` shows the natural-number subtraction never
truncates), `= 0` exactly when `P` is decomposable over `Γ`'s groups
(`couplingExcess_eq_zero_iff`), and `> 0` exactly when `P` genuinely couples
across the groups (`couplingExcess_pos_of_not_le`). -/
def couplingExcess (P Γ : Setoid α) : ℕ := rank P - rank (P ⊓ Γ)

theorem couplingExcess_eq_zero_iff : couplingExcess P Γ = 0 ↔ P ≤ Γ := by
  unfold couplingExcess
  constructor
  · intro h0
    by_contra hnle
    have hlt := rank_inf_lt_of_not_le P Γ hnle
    omega
  · intro hle
    have heq := rank_inf_eq_of_le P Γ hle
    omega

theorem couplingExcess_pos_of_not_le (h : ¬ P ≤ Γ) : 0 < couplingExcess P Γ := by
  unfold couplingExcess
  have := rank_inf_lt_of_not_le P Γ h
  omega

/-!
## Concrete witnesses on `Fin 4`

Guard against vacuity: exhibit an actual decomposable reading and an actual
coupled reading against the two-group split `splitΓ` of `Fin 4`, pairing
`{0, 1}` and `{2, 3}`.
-/

/-- The two-group split of `Fin 4`: blocks `{0, 1}` and `{2, 3}`, realized
as the kernel of the group-index map. -/
def splitΓ : Setoid (Fin 4) :=
  Setoid.ker (fun x : Fin 4 => if x.val < 2 then (0 : Fin 2) else 1)

/-- A DECOMPOSABLE reading: merges only within the first group (elements
`0` and `1`). It refines `splitΓ`, so reading it against the split loses no
rank. -/
def Pdec : Setoid (Fin 4) := mergePair (⊥ : Setoid (Fin 4)) 0 1

theorem Pdec_le_splitΓ : Pdec ≤ splitΓ := by
  have hΓ01 : splitΓ 0 1 := Setoid.ker_def.mpr (by decide)
  exact mergePair_le bot_le hΓ01

/-- Concrete witness of the decomposable case: zero coupling excess. -/
theorem couplingExcess_Pdec_splitΓ_eq_zero : couplingExcess Pdec splitΓ = 0 :=
  (couplingExcess_eq_zero_iff Pdec splitΓ).mpr Pdec_le_splitΓ

/-- A COUPLED reading: merges *across* the two groups (elements `1` and
`2`, one from each block of `splitΓ`). It does not refine `splitΓ`, so
reading it against the split strictly loses rank. -/
def Pcpl : Setoid (Fin 4) := mergePair (⊥ : Setoid (Fin 4)) 1 2

theorem not_Pcpl_le_splitΓ : ¬ Pcpl ≤ splitΓ := by
  intro hle
  have h12 : Pcpl 1 2 := mergePair_rel _ 1 2
  have hΓ12 : splitΓ 1 2 := hle h12
  have hne : (fun x : Fin 4 => if x.val < 2 then (0 : Fin 2) else 1) 1
      ≠ (fun x : Fin 4 => if x.val < 2 then (0 : Fin 2) else 1) 2 := by decide
  exact hne (Setoid.ker_def.mp hΓ12)

/-- Concrete witness of the coupling case: strictly positive coupling
excess. -/
theorem couplingExcess_Pcpl_splitΓ_pos : 0 < couplingExcess Pcpl splitΓ :=
  couplingExcess_pos_of_not_le Pcpl splitΓ not_Pcpl_le_splitΓ

end

end STE
