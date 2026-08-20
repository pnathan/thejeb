/-
Shannon's lattice-theoretic reading of STE coreference.

Shannon, "The Lattice Theory of Information" (IRE Transactions on Information
Theory, 1953), views an information source as a partition of a fixed sample
space, ordered by refinement, and shows that entropy is a rank function on
that lattice: `H(A ∨ B) + H(A ∧ B) ≤ H(A) + H(B)`.  The dynamic-frame STE
development (`Ste.DynamicFrame`) already lives in this lattice implicitly.
Each feasible normalization hypothesis `h` induces an exact coreference
partition of `Claim` (`sameFrame h`), and `mustSetoid D`, the must-coreference
relation over the feasible set, is their common refinement.

This module makes the lattice structure explicit in three steps.

* Part A (`STE.DynamicFrame.Model`) identifies the feasible coreference
  partitions as elements of Mathlib's complete lattice `Setoid Claim`, and
  shows `mustSetoid` is literally the infimum (`sInf`) of the feasible image.
* Part B (`STE.PartitionRank`) equips the partition lattice of a finite
  carrier with the combinatorial rank `r(P) = |α| − #blocks(P)`, and proves
  it is submodular: the metric-free, "lighter than a metric" counting
  analogue of entropy submodularity in Shannon's information lattice, taken
  on the order-dual side (`rank` is a co-entropy).
* Part C transfers the rank inequalities back to the STE must-partition.
-/
import Ste.DynamicFrame
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Basic

namespace STE.DynamicFrame.Model

universe uDoc uClaim uFrame uHypothesis uConstraint

variable {Document : Type uDoc} {Claim : Type uClaim} {Frame : Type uFrame}
variable {Hypothesis : Type uHypothesis} {Constraint : Type uConstraint}
variable (M : Model Document Claim Frame Hypothesis Constraint)

/-- The exact coreference partition induced by one normalization hypothesis,
as an element of Mathlib's complete lattice `Setoid Claim`. -/
def frameSetoid (h : Hypothesis) : Setoid Claim :=
  ⟨M.sameFrame h, M.sameFrame_equivalence h⟩

/-- Must-coreference IS the lattice meet (common refinement) of the feasible
partitions, in Mathlib's complete lattice `Setoid Claim`.  This is Shannon's
lattice reading of "the STE consensus source": `mustSetoid` is the common
information forced by every surviving hypothesis, i.e. the infimum of their
partitions under Mathlib's `Setoid` order. -/
theorem mustSetoid_eq_sInf (D : Set Document) :
    M.mustSetoid D = sInf (M.frameSetoid '' M.feasible D) := by
  apply Setoid.ext
  intro c d
  show M.MustSame D c d ↔ sInf (M.frameSetoid '' M.feasible D) c d
  rw [Setoid.sInf_iff, Set.forall_mem_image]
  rfl

/-- Every feasible hypothesis' exact partition refines the must-partition:
the meet is below every element of the feasible image. -/
theorem mustSetoid_le_frameSetoid {D : Set Document} {h : Hypothesis}
    (hh : h ∈ M.feasible D) : M.mustSetoid D ≤ M.frameSetoid h := by
  rw [mustSetoid_eq_sInf]
  exact sInf_le (Set.mem_image_of_mem M.frameSetoid hh)

/-- Adding documents can only add forced identifications: the must-partition
is monotone in the corpus, in the `Setoid` refinement order. -/
theorem mustSetoid_mono {D E : Set Document} (hDE : D ⊆ E) :
    M.mustSetoid D ≤ M.mustSetoid E := by
  intro c d h
  exact M.mustSame_mono hDE h

end STE.DynamicFrame.Model

/-!
## Part B: block count and rank on the partition lattice, and submodularity

The partition lattice of a finite carrier `α` is a geometric lattice; its
rank function `r(P) = |α| − #blocks(P)` is the order-dual (co-entropy)
counting analogue of Shannon entropy on the information lattice: the
submodular shape is the same, `r(A ⊔ B) + r(A ⊓ B) ≤ r(A) + r(B)`, but the
monotonicity direction is opposite — entropy increases under refinement,
`r` increases under coarsening (`r(⊥) = 0`, `r(⊤) = |α| − 1`).  See the
header of `Ste.InfoDistance` for the full dictionary relating `⊓`/`⊔` here
to Shannon's joint `∨` and common information `∧`.
-/

namespace STE.PartitionRank

variable {α : Type*} [Fintype α]

noncomputable section

open scoped Classical

/-- Number of blocks of the partition `s`. -/
noncomputable def blockCount (s : Setoid α) : ℕ := Fintype.card (Quotient s)

/-- Shannon-style combinatorial rank of a partition: carrier size minus block
count.  This is the rank function of the partition lattice (a geometric
lattice), and `rank_submodular` shows it is submodular — the order-dual
(co-entropy) counting analogue of entropy submodularity in Shannon's 1953
information lattice: same submodular shape, opposite monotonicity direction
(`rank` grows under coarsening, entropy under refinement). -/
noncomputable def rank (s : Setoid α) : ℕ := Fintype.card α - blockCount s

theorem blockCount_le_card (s : Setoid α) : blockCount s ≤ Fintype.card α :=
  Fintype.card_quotient_le s

theorem one_le_blockCount [Nonempty α] (s : Setoid α) : 1 ≤ blockCount s :=
  haveI : Nonempty (Quotient s) := ⟨Quotient.mk s (Classical.arbitrary α)⟩
  Fintype.card_pos

/-- Coarsening a partition can only decrease its block count. -/
theorem blockCount_antitone {s t : Setoid α} (h : s ≤ t) :
    blockCount t ≤ blockCount s :=
  Fintype.card_le_of_surjective (Setoid.map_of_le h)
    (Quotient.ind fun x => ⟨Quotient.mk s x, rfl⟩)

/-- If `s` refines `t` and some pair `u, v` is genuinely merged by `t` but
not related in `s`, the block count strictly drops. -/
theorem blockCount_lt {s t : Setoid α} (hst : s ≤ t) {u v : α}
    (hs : ¬ s u v) (ht : t u v) : blockCount t < blockCount s := by
  refine Fintype.card_lt_of_surjective_not_injective (Setoid.map_of_le hst)
    (Quotient.ind fun x => ⟨Quotient.mk s x, rfl⟩) ?_
  intro hinj
  apply hs
  have : Setoid.map_of_le hst (Quotient.mk s u) = Setoid.map_of_le hst (Quotient.mk s v) := by
    show Quotient.mk t u = Quotient.mk t v
    exact Quotient.sound' ht
  have huv := hinj this
  exact Quotient.exact' huv

theorem rank_le_rank {s t : Setoid α} (h : s ≤ t) : rank s ≤ rank t :=
  Nat.sub_le_sub_left (blockCount_antitone h) (Fintype.card α)

/-- Merge the blocks of `u` and `v` in `s`, leaving every other block
unchanged. -/
def mergePair (s : Setoid α) (u v : α) : Setoid α where
  r x y := s x y ∨ (s x u ∧ s v y) ∨ (s x v ∧ s u y)
  iseqv := by
    refine ⟨fun x => Or.inl (s.refl' x), ?_, ?_⟩
    · rintro x y (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl (s.symm' h)
      · exact Or.inr (Or.inr ⟨s.symm' h2, s.symm' h1⟩)
      · exact Or.inr (Or.inl ⟨s.symm' h2, s.symm' h1⟩)
    · rintro x y z (hxy | ⟨hxu, hvy⟩ | ⟨hxv, huy⟩) (hyz | ⟨hyu, hvz⟩ | ⟨hyv, huz⟩)
      · exact Or.inl (s.trans' hxy hyz)
      · exact Or.inr (Or.inl ⟨s.trans' hxy hyu, hvz⟩)
      · exact Or.inr (Or.inr ⟨s.trans' hxy hyv, huz⟩)
      · exact Or.inr (Or.inl ⟨hxu, s.trans' hvy hyz⟩)
      · exact Or.inr (Or.inl ⟨hxu, hvz⟩)
      · exact Or.inl (s.trans' hxu huz)
      · exact Or.inr (Or.inr ⟨hxv, s.trans' huy hyz⟩)
      · exact Or.inl (s.trans' hxv hvz)
      · exact Or.inr (Or.inr ⟨hxv, huz⟩)

omit [Fintype α] in
theorem le_mergePair (s : Setoid α) (u v : α) : s ≤ mergePair s u v :=
  fun _ _ h => Or.inl h

omit [Fintype α] in
theorem mergePair_rel (s : Setoid α) (u v : α) : mergePair s u v u v :=
  Or.inr (Or.inl ⟨s.refl' u, s.refl' v⟩)

omit [Fintype α] in
theorem mergePair_le {s t : Setoid α} {u v : α} (hst : s ≤ t) (huv : t u v) :
    mergePair s u v ≤ t := by
  rintro x y (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact hst h
  · exact t.trans' (hst h1) (t.trans' huv (hst h2))
  · exact t.trans' (hst h1) (t.trans' (t.symm' huv) (hst h2))

/-- Merging one previously-unrelated pair drops the block count by exactly
one.  This is the key counting engine behind submodularity. -/
theorem blockCount_mergePair {s : Setoid α} {u v : α} (h : ¬ s u v) :
    blockCount (mergePair s u v) + 1 = blockCount s := by
  haveI : Nonempty α := ⟨u⟩
  let φ : Quotient s → Quotient (mergePair s u v) := Quotient.map' id (fun _ _ => Or.inl)
  have hne : (Quotient.mk s v : Quotient s) ≠ Quotient.mk s u := by
    intro he
    exact h (s.symm' (Quotient.exact' he))
  have hbij : Function.Bijective (fun c : {c : Quotient s // c ≠ Quotient.mk s v} => φ c.1) := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      induction x using Quotient.ind' with
      | _ x =>
        induction y using Quotient.ind' with
        | _ y =>
          apply Subtype.ext
          rcases (Quotient.exact' hxy : mergePair s u v x y) with hr | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Quotient.sound' hr
          · exact absurd (Quotient.sound' h2).symm hy
          · exact absurd (Quotient.sound' h1) hx
    · intro q
      induction q using Quotient.ind' with
      | _ x =>
        by_cases hxv : (Quotient.mk s x : Quotient s) = Quotient.mk s v
        · refine ⟨⟨Quotient.mk s u, hne.symm⟩, ?_⟩
          show φ (Quotient.mk s u) = φ (Quotient.mk s x)
          show Quotient.mk (mergePair s u v) u = Quotient.mk (mergePair s u v) x
          have hxv' : s x v := Quotient.exact' hxv
          exact Quotient.sound' (Or.inr (Or.inl ⟨s.refl' u, s.symm' hxv'⟩))
        · exact ⟨⟨Quotient.mk s x, hxv⟩, rfl⟩
  have hcard : Fintype.card {c : Quotient s // c ≠ Quotient.mk s v} =
      blockCount (mergePair s u v) :=
    Fintype.card_congr (Equiv.ofBijective _ hbij)
  have hcompl : Fintype.card {c : Quotient s // c ≠ Quotient.mk s v} = blockCount s - 1 := by
    have := Fintype.card_subtype_compl (fun c : Quotient s => c = Quotient.mk s v)
    simp only [ne_eq, Fintype.card_subtype_eq, blockCount] at this ⊢
    exact this
  have hpos : 1 ≤ blockCount s := one_le_blockCount s
  omega

/-- Supermodularity of the block-count on the partition lattice of a finite
carrier: `#blocks(A) + #blocks(B) ≤ #blocks(A ⊔ B) + #blocks(A ⊓ B)`.
Equivalently (see `rank_submodular`) the partition-lattice rank is
submodular — the finite, metric-free counting analogue of entropy
submodularity in Shannon's 1953 information lattice, on the order-dual
(co-entropy) side. -/
theorem blockCount_supermodular (A B : Setoid α) :
    blockCount A + blockCount B ≤ blockCount (A ⊔ B) + blockCount (A ⊓ B) := by
  suffices h : ∀ n, ∀ A B : Setoid α, blockCount A ≤ n →
      blockCount A + blockCount B ≤ blockCount (A ⊔ B) + blockCount (A ⊓ B) by
    exact h (blockCount A) A B le_rfl
  intro n
  induction n with
  | zero =>
    intro A B hA
    have : IsEmpty (Quotient A) := Fintype.card_eq_zero_iff.mp (Nat.le_zero.mp hA)
    have hα : IsEmpty α := ⟨fun a => this.elim (Quotient.mk A a)⟩
    have hcard0 : Fintype.card α = 0 := Fintype.card_eq_zero_iff.mpr hα
    have hallzero : ∀ s : Setoid α, blockCount s = 0 := fun s =>
      Nat.le_zero.mp (hcard0 ▸ blockCount_le_card s)
    simp [hallzero]
  | succ n ih =>
    intro A B hA
    by_cases hBA : B ≤ A
    · have hsup : A ⊔ B = A := sup_eq_left.mpr hBA
      have hinf : A ⊓ B = B := le_antisymm inf_le_right (le_inf hBA le_rfl)
      rw [hsup, hinf]
    · have hex : ∃ u v, B u v ∧ ¬ A u v := by
        by_contra hcon
        push_neg at hcon
        exact hBA (fun {u v} huv => hcon u v huv)
      obtain ⟨u, v, hBuv, hAuv⟩ := hex
      set A' := mergePair A u v with hA'def
      have hle : A ≤ A' := le_mergePair A u v
      have hbc : blockCount A' + 1 = blockCount A := blockCount_mergePair hAuv
      have hsup : A' ⊔ B = A ⊔ B := by
        apply le_antisymm
        · exact sup_le (mergePair_le le_sup_left (Setoid.le_def.mp le_sup_right hBuv)) le_sup_right
        · exact sup_le_sup_right hle B
      have hinf : A ⊓ B ≤ A' ⊓ B := inf_le_inf hle le_rfl
      have hnAB : ¬ (A ⊓ B) u v := fun hcontra => hAuv hcontra.1
      have hA'B : (A' ⊓ B) u v := ⟨mergePair_rel A u v, hBuv⟩
      have hlt : blockCount (A' ⊓ B) < blockCount (A ⊓ B) :=
        blockCount_lt hinf hnAB hA'B
      have hAn : blockCount A' ≤ n := by omega
      have hind := ih A' B hAn
      rw [hsup] at hind
      omega

/-- Submodularity of the partition-lattice rank `r(P) = |α| - #blocks(P)`:
`r(A ⊔ B) + r(A ⊓ B) ≤ r(A) + r(B)`.  This has the shape of Shannon's
information-lattice inequality with the counting co-entropy `rank` in place
of entropy; the operator roles are order-dual to Shannon's (`⊓` is the joint
`∨`, `⊔` the common information `∧`), so the sum is the same but the
monotonicity reading is reversed. -/
theorem rank_submodular (A B : Setoid α) :
    rank (A ⊔ B) + rank (A ⊓ B) ≤ rank A + rank B := by
  have hsm := blockCount_supermodular A B
  have h1 := blockCount_le_card A
  have h2 := blockCount_le_card B
  have h3 := blockCount_le_card (A ⊔ B)
  have h4 := blockCount_le_card (A ⊓ B)
  simp only [rank]
  omega

end

end STE.PartitionRank

/-!
## Part C: transfer to STE must-coreference
-/

namespace STE.DynamicFrame.Model

universe uDoc' uClaim' uFrame' uHypothesis' uConstraint'

variable {Document : Type uDoc'} {Claim : Type uClaim'} {Frame : Type uFrame'}
variable {Hypothesis : Type uHypothesis'} {Constraint : Type uConstraint'}
variable (M : Model Document Claim Frame Hypothesis Constraint) [Fintype Claim]

/-- The consensus (must) partition never carries more forced-merge
information (rank) than any single feasible hypothesis. -/
theorem rank_mustSetoid_le_frameSetoid {D : Set Document} {h : Hypothesis}
    (hh : h ∈ M.feasible D) :
    PartitionRank.rank (M.mustSetoid D) ≤ PartitionRank.rank (M.frameSetoid h) :=
  PartitionRank.rank_le_rank (M.mustSetoid_le_frameSetoid hh)

/-- Coreference information is monotone in the corpus: adding documents can
only increase the rank of the must-partition. -/
theorem rank_mustSetoid_mono {D E : Set Document} (hDE : D ⊆ E) :
    PartitionRank.rank (M.mustSetoid D) ≤ PartitionRank.rank (M.mustSetoid E) :=
  PartitionRank.rank_le_rank (M.mustSetoid_mono hDE)

/-- Shannon submodularity, instantiated on the must-partitions of two
corpora. -/
theorem rank_mustSetoid_submodular (D E : Set Document) :
    PartitionRank.rank (M.mustSetoid D ⊔ M.mustSetoid E)
      + PartitionRank.rank (M.mustSetoid D ⊓ M.mustSetoid E)
      ≤ PartitionRank.rank (M.mustSetoid D) + PartitionRank.rank (M.mustSetoid E) :=
  PartitionRank.rank_submodular (M.mustSetoid D) (M.mustSetoid E)

end STE.DynamicFrame.Model

/-!
## Coupling and rank: a conjecture

For a decomposable (rectangular/product) feasible family — cf.
`Ste.FrameRectangular` and `Ste.Factorization` — one expects the rank of the
must-partition to decompose additively across independent constraint
supports: if the feasible set factors as a product over disjoint claim
groups, `rank (mustSetoid D)` restricted to each group should sum to the
rank on the whole.  Conversely, when feasibility is genuinely coupled across
groups (the diagonal/non-rectangular case already shown obstructed in
`Ste.CechObstruction`), the rank of a join of per-group must-partitions
should be able to strictly exceed the sum of the per-group ranks, mirroring
how coupling raises joint entropy relative to independent components.

Making this precise is future work: it requires an entropy layer on top of
the present combinatorial rank — e.g. `H = log |feasible|` on the space of
hypotheses, related by the interpretation map to the partition lattice on
`Claim` — connecting hypothesis-space partitions to claim-space partitions.
The current development has the claim-space partition lattice and its
combinatorial rank, but not yet the hypothesis-space entropy or the map
between the two; we do not state a theorem here, only the target shape of
the eventual result.
-/
