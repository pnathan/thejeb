/-
Combinatorial Shannon distance on the partition lattice.

Delsol, Rioul, Béguinot, Rabiet, and Souloumiac (2024) revisit Shannon's 1953
information lattice and show the (extended) entropic distance
`D(X, Y) = H(X|Y) + H(Y|X) = 2 H(X, Y) - H(X) - H(Y)` is a genuine metric on
the lattice of partitions/sources.  This module mechanizes the finite,
metric-free "shadow" of that fact: with Shannon entropy replaced by the
combinatorial rank `STE.PartitionRank.rank` already built and shown
submodular in `Ste.PartitionRank`, the same distance formula is a metric on
the partition lattice of any finite carrier — no entropy is needed, only
`rank`'s monotonicity and submodularity.
-/
import Ste.PartitionRank

namespace STE.PartitionRank

variable {α : Type*} [Fintype α]

noncomputable section

open scoped Classical

/-- Combinatorial Shannon distance on the partition lattice: the counting
shadow of `D(X,Y) = H(X|Y) + H(Y|X)`.  Each summand `rank (P ⊔ Q) - rank P`
is a genuine (non-truncated) `ℕ` difference because `rank` is monotone and
`P ≤ P ⊔ Q`. -/
def shannonDist (P Q : Setoid α) : ℕ :=
  (rank (P ⊔ Q) - rank P) + (rank (P ⊔ Q) - rank Q)

/-- `rank` is monotone along the left leg of a join. -/
theorem rank_le_rank_sup_left (P Q : Setoid α) : rank P ≤ rank (P ⊔ Q) :=
  rank_le_rank le_sup_left

/-- `rank` is monotone along the right leg of a join. -/
theorem rank_le_rank_sup_right (P Q : Setoid α) : rank Q ≤ rank (P ⊔ Q) :=
  rank_le_rank le_sup_right

@[simp]
theorem shannonDist_self (P : Setoid α) : shannonDist P P = 0 := by
  simp [shannonDist]

theorem shannonDist_comm (P Q : Setoid α) : shannonDist P Q = shannonDist Q P := by
  simp only [shannonDist, sup_comm P Q]
  omega

/-- Key counting inequality behind the triangle inequality:
`rank (P ⊔ R) + rank Q ≤ rank (P ⊔ Q) + rank (Q ⊔ R)`. -/
theorem rank_sup_add_le (P Q R : Setoid α) :
    rank (P ⊔ R) + rank Q ≤ rank (P ⊔ Q) + rank (Q ⊔ R) := by
  have hsm := rank_submodular (P ⊔ Q) (Q ⊔ R)
  have hPR_le : P ⊔ R ≤ (P ⊔ Q) ⊔ (Q ⊔ R) := by
    apply sup_le
    · exact le_sup_of_le_left le_sup_left
    · exact le_sup_of_le_right le_sup_right
  have hQ_le : Q ≤ (P ⊔ Q) ⊓ (Q ⊔ R) := le_inf le_sup_right le_sup_left
  have h1 : rank (P ⊔ R) ≤ rank ((P ⊔ Q) ⊔ (Q ⊔ R)) := rank_le_rank hPR_le
  have h2 : rank Q ≤ rank ((P ⊔ Q) ⊓ (Q ⊔ R)) := rank_le_rank hQ_le
  omega

/-- The combinatorial Shannon distance satisfies the triangle inequality. -/
theorem shannonDist_triangle (P Q R : Setoid α) :
    shannonDist P R ≤ shannonDist P Q + shannonDist Q R := by
  have h1 := rank_le_rank_sup_left P Q
  have h2 := rank_le_rank_sup_right P Q
  have h3 := rank_le_rank_sup_left Q R
  have h4 := rank_le_rank_sup_right Q R
  have h5 := rank_le_rank_sup_left P R
  have h6 := rank_le_rank_sup_right P R
  have h7 := rank_sup_add_le P Q R
  simp only [shannonDist]
  omega

/-- If two partitions are related by refinement with equal rank, they
coincide.  Proved by contradiction via `blockCount_lt`: a strict refinement
that is not equality must strictly drop the block count, contradicting
`blockCount_le_card` once the ranks agree. -/
theorem eq_of_le_of_rank_eq {s t : Setoid α} (hle : s ≤ t) (hr : rank s = rank t) :
    s = t := by
  by_contra hne
  have hnot : ¬ t ≤ s := by
    intro hts
    exact hne (le_antisymm hle hts)
  have hex : ∃ u v, t u v ∧ ¬ s u v := by
    by_contra hcon
    push_neg at hcon
    exact hnot (fun {u v} huv => hcon u v huv)
  obtain ⟨u, v, htuv, hsuv⟩ := hex
  have hlt : blockCount t < blockCount s := blockCount_lt hle hsuv htuv
  have hcs := blockCount_le_card s
  have hct := blockCount_le_card t
  simp only [rank] at hr
  omega

/-- The combinatorial Shannon distance separates points: it vanishes exactly
on the diagonal. -/
theorem shannonDist_eq_zero_iff (P Q : Setoid α) : shannonDist P Q = 0 ↔ P = Q := by
  constructor
  · intro h
    have h1 := rank_le_rank_sup_left P Q
    have h2 := rank_le_rank_sup_right P Q
    simp only [shannonDist] at h
    have hP : rank P = rank (P ⊔ Q) := by omega
    have hQ : rank Q = rank (P ⊔ Q) := by omega
    have heP : P = P ⊔ Q := eq_of_le_of_rank_eq le_sup_left hP
    have heQ : Q = P ⊔ Q := eq_of_le_of_rank_eq le_sup_right hQ
    exact heP.trans heQ.symm
  · intro h
    rw [h]
    exact shannonDist_self Q

/-- Additivity along a chain: for partitions aligned as `P ≤ Q ≤ R`, the
combinatorial Shannon distance adds up exactly, mirroring the "aligned
points" behaviour of the entropic distance on a refinement chain. -/
theorem shannonDist_chain_add {P Q R : Setoid α} (hPQ : P ≤ Q) (hQR : Q ≤ R) :
    shannonDist P R = shannonDist P Q + shannonDist Q R := by
  have hPR : P ≤ R := le_trans hPQ hQR
  have heQ : P ⊔ Q = Q := sup_eq_right.mpr hPQ
  have heR : Q ⊔ R = R := sup_eq_right.mpr hQR
  have heR' : P ⊔ R = R := sup_eq_right.mpr hPR
  have h1 := rank_le_rank hPQ
  have h2 := rank_le_rank hQR
  simp only [shannonDist, heQ, heR, heR']
  omega

end

end STE.PartitionRank
