/-
Metric-lattice geometry of the combinatorial Shannon distance.

Delsol, Rioul, Béguinot, Rabiet, Souloumiac, "Towards a Theory of Information
Lattices" (2024; ingested at `sources/delsol2024/`), and Shannon's 1953 "The
Lattice Theory of Information" study the entropic distance `D` on the
information lattice as a metric-*geometric* object, not merely a metric.  On
a finite carrier the metric topology of `shannonDist` (built in
`Ste.InfoDistance` from the combinatorial rank of `Ste.PartitionRank`, an
order-dual counting analogue of `D` rather than `D` itself) is discrete:
every distinct pair of partitions is at distance `≥ 1`
(`one_le_shannonDist_of_ne`), so the metric *topology* carries no information beyond the discrete topology.  The
interesting structure is not topological but metric-geometric: which lattice
operations are contractions for `shannonDist`, what metric betweenness looks
like on the partition lattice, and whether the resulting finite metric space
embeds in `ℓ1` / is a median space.

## Which operator is which (see `Ste.InfoDistance` for the full dictionary)

The dictionary is stated once in the header of `Ste.InfoDistance` and is used
here without restatement.  In brief: in Mathlib's `Setoid α`, `⊓` is
intersection of relations = the common refinement = the **joint** source
`∨` of Shannon/Delsol; `⊔` is the coarsest common coarsening = the
**common-information** operator `∧`, the Gács–Körner operator; and `rank` is
a co-entropy, monotone under coarsening where `H` is monotone under
refinement.

## The counting shadow REVERSES the Delsol dichotomy

Delsol's metric-lattice picture is: the joint `∨` is well behaved (Prop. 20 /
Remark 11 give continuity and contraction statements for `∨`), while the
common information `∧` is badly behaved (Prop. 19: `∧` is discontinuous, the
Gács–Körner phenomenon).  What this file *proves* is the exact opposite
pairing:

* `⊔` — the common-information operator `∧` — **is** a metric contraction
  and jointly 1-Lipschitz for `shannonDist`
  (`shannonDist_sup_right_le`, `shannonDist_sup_le_add`).
* `⊓` — the **joint** `∨` — is **not** a contraction, already on a carrier
  of size 4 (`shannonDist_inf_not_contraction`), with no uniform Lipschitz
  constant at all (`Ste.MeetScaling.meet_not_lipschitz`).

This is a reversal of Delsol's dichotomy, not a reproduction of it, and it
should be read as a fact about the shadow rather than as evidence for the
entropic statements.  The mechanism is the co-entropy: `rank` is
anti-monotone in information, so passing from `H` to `rank` passes to the
order-dual lattice and exchanges the roles of the two operators.  A
contraction result for `⊔` in the counting shadow is therefore the dual-side
analogue of Delsol's `∨` results, and carries no direct implication for
Delsol's `∧`; likewise the failure below is a counting-shadow failure for
`⊓`, not a mechanization of Prop. 19.  Cited proposition numbers below mark
the *source of the shape* of each statement, never a claim that the
entropic result has been transported.

Further negative result, independent of the above (the pentagonal inequality
of Deza–Laurent, "Geometry of Cuts and Metrics"): already for `|α| = 3` the
partition metric space violates the pentagonal inequality — its covering
graph on the three atoms plus `⊥, ⊤` is `K_{2,3}` — hence `shannonDist` is
neither `ℓ1`-embeddable nor a median metric.
-/
import Ste.InfoDistance
import Mathlib.Tactic.FinCases

namespace STE.PartitionRank

variable {α : Type*} [Fintype α]

noncomputable section

open scoped Classical

/-! ## Part 1: discreteness marker (honest triviality) -/

/-- Shannon 1953 / Delsol 2024: the combinatorial Shannon distance separates
points by at least `1`.  Consequently the metric topology it induces on the
(finite) partition lattice is the discrete topology, and every further
result in this file is genuinely metric-*geometric* content, not topological
content. -/
theorem one_le_shannonDist_of_ne {P Q : Setoid α} (h : P ≠ Q) : 1 ≤ shannonDist P Q :=
  Nat.one_le_iff_ne_zero.mpr (fun h0 => h ((shannonDist_eq_zero_iff P Q).mp h0))

/-! ## Part 2: parity / bipartiteness -/

/-- The combinatorial Shannon distance has the parity of `rank P + rank Q`:
`shannonDist` is the covering-graph (Hasse) distance formula
`2 r(P ⊔ Q) − r(P) − r(Q)` of the upper-semimodular partition lattice, so the
metric space is "bipartite" like a hypercube skeleton (Shannon 1953). We do
not mechanize the graph-distance identification itself, only this parity
witness. -/
theorem shannonDist_add_rank_add_rank (P Q : Setoid α) :
    shannonDist P Q + rank P + rank Q = 2 * rank (P ⊔ Q) := by
  have h1 := rank_le_rank_sup_left P Q
  have h2 := rank_le_rank_sup_right P Q
  simp only [shannonDist]
  omega

/-! ## Part 3: `⊔` (common information) is a contraction -/

/-- Dual-side counting analogue of Delsol Remark 11,
`D(X ∨ Y, X ∨ Z) ≤ D(Y, Z)`: taking `⊔` with a fixed partition `R` is a
metric contraction for `shannonDist`, so `⊔` is uniformly continuous in each
argument — half of the "metric lattice" property.

Note the reversal flagged in the module docstring: `⊔` here is the
*common-information* operator `∧` (Gács–Körner), the one Delsol Prop. 19
shows is discontinuous in the entropic setting. Remark 11's shape is what is
reproduced, on the order-dual side, not its content. Contrast with
`shannonDist_inf_not_contraction` below, where the analogous statement for
the joint `⊓` fails. -/
theorem shannonDist_sup_right_le (P Q R : Setoid α) :
    shannonDist (P ⊔ R) (Q ⊔ R) ≤ shannonDist P Q := by
  have hW : (P ⊔ R) ⊔ (Q ⊔ R) = (P ⊔ Q) ⊔ R := by
    simp [sup_left_comm, sup_comm]
  have h1 : (P ⊔ R) ⊔ (P ⊔ Q) = (P ⊔ Q) ⊔ R := by
    simp [sup_left_comm, sup_comm]
  have h2 : (Q ⊔ R) ⊔ (P ⊔ Q) = (P ⊔ Q) ⊔ R := by
    simp [sup_left_comm, sup_comm]
  have hsm1 := rank_submodular (P ⊔ R) (P ⊔ Q)
  rw [h1] at hsm1
  have hsm2 := rank_submodular (Q ⊔ R) (P ⊔ Q)
  rw [h2] at hsm2
  have hP : rank P ≤ rank ((P ⊔ R) ⊓ (P ⊔ Q)) := rank_le_rank (le_inf le_sup_left le_sup_left)
  have hQ : rank Q ≤ rank ((Q ⊔ R) ⊓ (P ⊔ Q)) := rank_le_rank (le_inf le_sup_left le_sup_right)
  have m1 : rank (P ⊔ R) ≤ rank ((P ⊔ Q) ⊔ R) := rank_le_rank (sup_le_sup_right le_sup_left R)
  have m2 : rank (Q ⊔ R) ≤ rank ((P ⊔ Q) ⊔ R) := rank_le_rank (sup_le_sup_right le_sup_right R)
  have mP : rank P ≤ rank (P ⊔ Q) := rank_le_rank le_sup_left
  have mQ : rank Q ≤ rank (P ⊔ Q) := rank_le_rank le_sup_right
  simp only [shannonDist, hW]
  omega

/-- Dual-side counting analogue of Delsol Prop. 20: `⊔` is jointly
1-Lipschitz for `shannonDist` — the positive half of continuity of the
lattice operations in the metric-lattice structure. As in
`shannonDist_sup_right_le`, Prop. 20 is a positive continuity result for the
joint `∨`, whereas the operator that is 1-Lipschitz here is `⊔`, the
common-information `∧`. -/
theorem shannonDist_sup_le_add (P P' Q Q' : Setoid α) :
    shannonDist (P ⊔ Q) (P' ⊔ Q') ≤ shannonDist P P' + shannonDist Q Q' := by
  have hleg1 : shannonDist (P ⊔ Q) (P' ⊔ Q) ≤ shannonDist P P' :=
    shannonDist_sup_right_le P P' Q
  have hleg2 : shannonDist (P' ⊔ Q) (P' ⊔ Q') ≤ shannonDist Q Q' := by
    have h := shannonDist_sup_right_le Q Q' P'
    rw [sup_comm P' Q, sup_comm P' Q']
    exact h
  calc shannonDist (P ⊔ Q) (P' ⊔ Q')
      ≤ shannonDist (P ⊔ Q) (P' ⊔ Q) + shannonDist (P' ⊔ Q) (P' ⊔ Q') :=
        shannonDist_triangle _ _ _
    _ ≤ shannonDist P P' + shannonDist Q Q' := by omega

/-! ## Part 4: betweenness (extends `shannonDist_chain_add`) -/

/-- Dual-side counting analogue of Delsol Prop. 22 (alignment for the Shannon
distance `D`, i.e. `X`–`Y`–`Z` a Markov chain and `Y ≤ X ∨ Z`): metric
betweenness for `shannonDist` forces the two lattice conditions `Q ≤ P ⊔ R`
(the "function of the endpoints" condition) and `Q = (P ⊔ Q) ⊓ (Q ⊔ R)` (the
combinatorial Markov condition).

Note on the correspondence: the `∨` in Prop. 22 is the *joint*, which under
the dictionary of `Ste.InfoDistance` is Mathlib's `⊓`; the conclusion
mechanized here, `Q ≤ P ⊔ R`, therefore sits on the order-dual side of that
statement rather than being its transport. Only this one direction is
proved. The converse fails in general because the partition
lattice is not modular: equality in submodularity additionally requires
`(P ⊔ Q, Q ⊔ R)` to be a modular pair. This strictly extends
`shannonDist_chain_add` (chains satisfy both conditions; see
`aligned_of_chain`). -/
theorem le_sup_of_aligned {P Q R : Setoid α}
    (h : shannonDist P Q + shannonDist Q R = shannonDist P R) :
    Q ≤ P ⊔ R ∧ Q = (P ⊔ Q) ⊓ (Q ⊔ R) := by
  have hsup : (P ⊔ Q) ⊔ (Q ⊔ R) = (P ⊔ Q) ⊔ R := by
    simp [sup_left_comm, sup_comm]
  have hsm := rank_submodular (P ⊔ Q) (Q ⊔ R)
  rw [hsup] at hsm
  have hQm : rank Q ≤ rank ((P ⊔ Q) ⊓ (Q ⊔ R)) := rank_le_rank (le_inf le_sup_right le_sup_left)
  have hPR_le : P ⊔ R ≤ (P ⊔ Q) ⊔ R := sup_le_sup_right le_sup_left R
  have hPR : rank (P ⊔ R) ≤ rank ((P ⊔ Q) ⊔ R) := rank_le_rank hPR_le
  have h1 := rank_le_rank_sup_left P Q
  have h2 := rank_le_rank_sup_right P Q
  have h3 := rank_le_rank_sup_left Q R
  have h4 := rank_le_rank_sup_right Q R
  have h5 := rank_le_rank_sup_left P R
  have h6 := rank_le_rank_sup_right P R
  simp only [shannonDist] at h
  have eq1 : rank (P ⊔ R) = rank ((P ⊔ Q) ⊔ R) := by omega
  have eq2 : rank Q = rank ((P ⊔ Q) ⊓ (Q ⊔ R)) := by omega
  refine ⟨?_, eq_of_le_of_rank_eq (le_inf le_sup_right le_sup_left) eq2⟩
  have e1 : P ⊔ R = (P ⊔ Q) ⊔ R := eq_of_le_of_rank_eq hPR_le eq1
  calc Q ≤ P ⊔ Q := le_sup_right
    _ ≤ (P ⊔ Q) ⊔ R := le_sup_left
    _ = P ⊔ R := e1.symm

/-- Sanity corollary: chains satisfy the alignment hypothesis, so
`le_sup_of_aligned` recovers the two betweenness conditions for any chain
`P ≤ Q ≤ R`. -/
theorem aligned_of_chain {P Q R : Setoid α} (hPQ : P ≤ Q) (hQR : Q ≤ R) :
    Q ≤ P ⊔ R ∧ Q = (P ⊔ Q) ⊓ (Q ⊔ R) :=
  le_sup_of_aligned ((shannonDist_chain_add hPQ hQR).symm)

/-! ## Part 5: small-instance infrastructure -/

/-- Shannon 1953: the discrete partition `⊥` (every block a singleton) has as
many blocks as the carrier has points — the "finest source". -/
theorem blockCount_bot : blockCount (⊥ : Setoid α) = Fintype.card α :=
  Fintype.card_congr Setoid.quotientBotEquiv

/-- Shannon 1953: the one-block partition `⊤` (every point identified) has a
single block — the "coarsest source". -/
theorem blockCount_top [Nonempty α] : blockCount (⊤ : Setoid α) = 1 := by
  show Fintype.card (Quotient (⊤ : Setoid α)) = 1
  rw [Fintype.card_eq_one_iff]
  refine ⟨Quotient.mk ⊤ (Classical.arbitrary α), fun y => ?_⟩
  induction y using Quotient.ind with
  | _ y => exact Quotient.sound' (Setoid.eq_top_iff.mp rfl y (Classical.arbitrary α))

/-- Shannon 1953: the discrete partition has rank `0` — it carries no
forced-merge information, the bottom of the rank function. -/
theorem rank_bot : rank (⊥ : Setoid α) = 0 := by
  unfold rank
  rw [blockCount_bot]
  omega

/-- Shannon 1953: the one-block partition has the maximal rank `|α| - 1` —
the top of the (upper-semimodular) partition-lattice rank function. -/
theorem rank_top [Nonempty α] : rank (⊤ : Setoid α) = Fintype.card α - 1 := by
  unfold rank
  rw [blockCount_top]

/-- `⊥ ⊔ P = P` (`bot_sup_eq`), so taking the lattice join `⊔` with the
discrete partition is the identity for `shannonDist`. -/
theorem shannonDist_bot (P : Setoid α) : shannonDist ⊥ P = rank P := by
  simp only [shannonDist, bot_sup_eq, rank_bot]
  omega

/-- `⊤ ⊔ P = ⊤` (`top_sup_eq`), so taking the lattice join `⊔` with the
one-block partition
collapses `shannonDist` to the rank gap from `⊤`. -/
theorem shannonDist_top (P : Setoid α) : shannonDist ⊤ P = rank (⊤ : Setoid α) - rank P := by
  simp only [shannonDist, top_sup_eq]
  have h1 : rank P ≤ rank (⊤ : Setoid α) := rank_le_rank le_top
  omega

/-! ## Part 6: `⊓` (the joint) is NOT a contraction (Fin 4 counterexample) -/

/-- The joint operator `⊓` fails to be a contraction for `shannonDist`.

This is the reversal recorded in the module docstring: Delsol's negative
result (Prop. 19, discontinuity, the Gács–Körner phenomenon) is about the
common-information operator `∧` = Mathlib's `⊔`, which is a contraction here
(`shannonDist_sup_right_le`); his Prop. 20 / Remark 11 are *positive*
continuity results for the joint `∨` = Mathlib's `⊓`, which is what fails
below. The failure is a property of the counting shadow, driven by `rank`
being a co-entropy, not a mechanization of Prop. 19.

On a carrier of size `2k` the
gap scales: `d(⊤, {top-half | bottom-half}) = 1` while meeting with the
perfect-matching partition sends it to `d = k`; so meet admits *no* Lipschitz
constant uniform in the carrier. We mechanize the `k = 2` instance: the
matching partitions `{0,1},{2,3}` and `{0,2},{1,3}` of `Fin 4`. -/
theorem shannonDist_inf_not_contraction :
    ∃ P Q R : Setoid (Fin 4), shannonDist P Q < shannonDist (P ⊓ R) (Q ⊓ R) := by
  set Q4 : Setoid (Fin 4) := mergePair (mergePair ⊥ 0 1) 2 3 with hQ4def
  set R4 : Setoid (Fin 4) := mergePair (mergePair ⊥ 0 2) 1 3 with hR4def
  have hne01 : ¬ (⊥ : Setoid (Fin 4)) 0 1 := by
    rw [Setoid.bot_def]; decide
  have hne23 : ¬ (mergePair (⊥ : Setoid (Fin 4)) 0 1) 2 3 := by
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
  have hne02 : ¬ (⊥ : Setoid (Fin 4)) 0 2 := by
    rw [Setoid.bot_def]; decide
  have hne13 : ¬ (mergePair (⊥ : Setoid (Fin 4)) 0 2) 1 3 := by
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
  have hbcQ1 : blockCount (mergePair (⊥ : Setoid (Fin 4)) 0 1) + 1 = blockCount ⊥ :=
    blockCount_mergePair hne01
  have hbcQ2 : blockCount Q4 + 1 = blockCount (mergePair (⊥ : Setoid (Fin 4)) 0 1) := by
    rw [hQ4def]; exact blockCount_mergePair hne23
  have hbcR1 : blockCount (mergePair (⊥ : Setoid (Fin 4)) 0 2) + 1 = blockCount ⊥ :=
    blockCount_mergePair hne02
  have hbcR2 : blockCount R4 + 1 = blockCount (mergePair (⊥ : Setoid (Fin 4)) 0 2) := by
    rw [hR4def]; exact blockCount_mergePair hne13
  have hbot4 : blockCount (⊥ : Setoid (Fin 4)) = Fintype.card (Fin 4) := blockCount_bot
  have hcard4 : Fintype.card (Fin 4) = 4 := Fintype.card_fin 4
  have hbcQ4 : blockCount Q4 = 2 := by omega
  have hbcR4 : blockCount R4 = 2 := by omega
  have hrQ4 : rank Q4 = 2 := by unfold rank; rw [hbcQ4, hcard4]
  have hrR4 : rank R4 = 2 := by unfold rank; rw [hbcR4, hcard4]
  have htinf : (⊤ : Setoid (Fin 4)) ⊓ R4 = R4 := top_inf_eq R4
  have htsup : (⊤ : Setoid (Fin 4)) ⊔ Q4 = ⊤ := top_sup_eq Q4
  -- Single-level negations for the inner merges `A := mergePair ⊥ 0 1`
  -- (used by `Q4`) and `B := mergePair ⊥ 0 2` (used by `R4`), each a cheap
  -- one-step case bash exactly like `hne23`/`hne13` above.
  have hnA02 : ¬ (mergePair (⊥ : Setoid (Fin 4)) 0 1) 0 2 := by
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
  have hnA03 : ¬ (mergePair (⊥ : Setoid (Fin 4)) 0 1) 0 3 := by
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
  have hnA12 : ¬ (mergePair (⊥ : Setoid (Fin 4)) 0 1) 1 2 := by
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
  have hnA13 : ¬ (mergePair (⊥ : Setoid (Fin 4)) 0 1) 1 3 := by
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
  have hnB01 : ¬ (mergePair (⊥ : Setoid (Fin 4)) 0 2) 0 1 := by
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
  have hnB03 : ¬ (mergePair (⊥ : Setoid (Fin 4)) 0 2) 0 3 := by
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
  have hnB21 : ¬ (mergePair (⊥ : Setoid (Fin 4)) 0 2) 2 1 := by
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
  have hnB23 : ¬ (mergePair (⊥ : Setoid (Fin 4)) 0 2) 2 3 := by
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all
  -- Six top-level facts, each combining two of the single-level negations
  -- above through one more layer of `mergePair`'s three-way disjunction.
  have hnQ02 : ¬ Q4 0 2 := by
    rw [hQ4def]
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hnA02 h
    · exact hnA02 h1
    · exact hnA03 h1
  have hnQ03 : ¬ Q4 0 3 := by
    rw [hQ4def]
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hnA03 h
    · exact hnA02 h1
    · exact hnA03 h1
  have hnQ12 : ¬ Q4 1 2 := by
    rw [hQ4def]
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hnA12 h
    · exact hnA12 h1
    · exact hnA13 h1
  have hnQ13 : ¬ Q4 1 3 := by
    rw [hQ4def]
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hnA13 h
    · exact hnA12 h1
    · exact hnA13 h1
  have hnR01 : ¬ R4 0 1 := by
    rw [hR4def]
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hnB01 h
    · exact hnB01 h1
    · exact hnB03 h1
  have hnR23 : ¬ R4 2 3 := by
    rw [hR4def]
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hnB23 h
    · exact hnB21 h1
    · exact hnB23 h1
  have hnQ20 : ¬ Q4 2 0 := fun h => hnQ02 (Q4.symm' h)
  have hnQ30 : ¬ Q4 3 0 := fun h => hnQ03 (Q4.symm' h)
  have hnQ21 : ¬ Q4 2 1 := fun h => hnQ12 (Q4.symm' h)
  have hnQ31 : ¬ Q4 3 1 := fun h => hnQ13 (Q4.symm' h)
  have hnR10 : ¬ R4 1 0 := fun h => hnR01 (R4.symm' h)
  have hnR32 : ¬ R4 3 2 := fun h => hnR23 (R4.symm' h)
  have hQR_bot : Q4 ⊓ R4 = (⊥ : Setoid (Fin 4)) := by
    apply le_antisymm _ bot_le
    intro x y hxy
    obtain ⟨hq, hr⟩ := Setoid.inf_iff_and.mp hxy
    fin_cases x <;> fin_cases y <;>
      first
        | rfl
        | exact absurd hr hnR01 | exact absurd hr hnR10
        | exact absurd hq hnQ02 | exact absurd hq hnQ20
        | exact absurd hq hnQ03 | exact absurd hq hnQ30
        | exact absurd hq hnQ12 | exact absurd hq hnQ21
        | exact absurd hq hnQ13 | exact absurd hq hnQ31
        | exact absurd hr hnR23 | exact absurd hr hnR32
  refine ⟨⊤, Q4, R4, ?_⟩
  have hd1 : shannonDist (⊤ : Setoid (Fin 4)) Q4 = 1 := by
    rw [shannonDist_top]
    have hrtop : rank (⊤ : Setoid (Fin 4)) = 3 := by
      rw [rank_top, hcard4]
    rw [hrtop, hrQ4]
  have hd2 : shannonDist ((⊤ : Setoid (Fin 4)) ⊓ R4) (Q4 ⊓ R4) = 2 := by
    rw [htinf, hQR_bot, shannonDist_comm, shannonDist_bot, hrR4]
  omega

/-! ## Part 7: not ℓ1, not median (Fin 3) -/

/-- The three two-block "atom" partitions of `Fin 3` (Deza–Laurent, "Geometry
of Cuts and Metrics"; Delsol et al. 2024, §4): used for the
pentagonal-inequality and non-median counterexamples below. -/
private noncomputable def a3 : Setoid (Fin 3) := mergePair ⊥ 0 1

private noncomputable def b3 : Setoid (Fin 3) := mergePair ⊥ 0 2

private noncomputable def c3 : Setoid (Fin 3) := mergePair ⊥ 1 2

/-- Auxiliary computation for Part 7: `a3` has two blocks. -/
private theorem blockCount_a3 : blockCount a3 = 2 := by
  show blockCount (mergePair (⊥ : Setoid (Fin 3)) 0 1) = 2
  have h : ¬ (⊥ : Setoid (Fin 3)) 0 1 := by rw [Setoid.bot_def]; decide
  have heq := blockCount_mergePair h
  have hbot : blockCount (⊥ : Setoid (Fin 3)) = 3 := by rw [blockCount_bot, Fintype.card_fin]
  omega

/-- Auxiliary computation for Part 7: `b3` has two blocks. -/
private theorem blockCount_b3 : blockCount b3 = 2 := by
  show blockCount (mergePair (⊥ : Setoid (Fin 3)) 0 2) = 2
  have h : ¬ (⊥ : Setoid (Fin 3)) 0 2 := by rw [Setoid.bot_def]; decide
  have heq := blockCount_mergePair h
  have hbot : blockCount (⊥ : Setoid (Fin 3)) = 3 := by rw [blockCount_bot, Fintype.card_fin]
  omega

/-- Auxiliary computation for Part 7: `c3` has two blocks. -/
private theorem blockCount_c3 : blockCount c3 = 2 := by
  show blockCount (mergePair (⊥ : Setoid (Fin 3)) 1 2) = 2
  have h : ¬ (⊥ : Setoid (Fin 3)) 1 2 := by rw [Setoid.bot_def]; decide
  have heq := blockCount_mergePair h
  have hbot : blockCount (⊥ : Setoid (Fin 3)) = 3 := by rw [blockCount_bot, Fintype.card_fin]
  omega

private theorem rank_a3 : rank a3 = 1 := by
  unfold rank; rw [blockCount_a3, Fintype.card_fin]

private theorem rank_b3 : rank b3 = 1 := by
  unfold rank; rw [blockCount_b3, Fintype.card_fin]

private theorem rank_c3 : rank c3 = 1 := by
  unfold rank; rw [blockCount_c3, Fintype.card_fin]

/-- Auxiliary computation for Part 7: the lattice join `⊔` of any two of the
three atoms is the one-block partition, since the atoms pairwise share a
point. -/
private theorem a3_sup_b3 : a3 ⊔ b3 = ⊤ := by
  have h01 : a3 0 1 := mergePair_rel (⊥ : Setoid (Fin 3)) 0 1
  have h02 : b3 0 2 := mergePair_rel (⊥ : Setoid (Fin 3)) 0 2
  have h01' : (a3 ⊔ b3) 0 1 := Setoid.le_def.mp le_sup_left h01
  have h02' : (a3 ⊔ b3) 0 2 := Setoid.le_def.mp le_sup_right h02
  have h10' : (a3 ⊔ b3) 1 0 := (a3 ⊔ b3).symm' h01'
  have h20' : (a3 ⊔ b3) 2 0 := (a3 ⊔ b3).symm' h02'
  have h12' : (a3 ⊔ b3) 1 2 := (a3 ⊔ b3).trans' h10' h02'
  have h21' : (a3 ⊔ b3) 2 1 := (a3 ⊔ b3).symm' h12'
  rw [Setoid.eq_top_iff]
  intro x y
  fin_cases x <;> fin_cases y <;>
    first | exact (a3 ⊔ b3).refl' _ | exact h01' | exact h02' | exact h10' | exact h20' | exact h12' | exact h21'

private theorem a3_sup_c3 : a3 ⊔ c3 = ⊤ := by
  have h01 : a3 0 1 := mergePair_rel (⊥ : Setoid (Fin 3)) 0 1
  have h12 : c3 1 2 := mergePair_rel (⊥ : Setoid (Fin 3)) 1 2
  have h01' : (a3 ⊔ c3) 0 1 := Setoid.le_def.mp le_sup_left h01
  have h12' : (a3 ⊔ c3) 1 2 := Setoid.le_def.mp le_sup_right h12
  have h02' : (a3 ⊔ c3) 0 2 := (a3 ⊔ c3).trans' h01' h12'
  have h10' : (a3 ⊔ c3) 1 0 := (a3 ⊔ c3).symm' h01'
  have h21' : (a3 ⊔ c3) 2 1 := (a3 ⊔ c3).symm' h12'
  have h20' : (a3 ⊔ c3) 2 0 := (a3 ⊔ c3).symm' h02'
  rw [Setoid.eq_top_iff]
  intro x y
  fin_cases x <;> fin_cases y <;>
    first | exact (a3 ⊔ c3).refl' _ | exact h01' | exact h12' | exact h02' | exact h10' | exact h21' | exact h20'

private theorem b3_sup_c3 : b3 ⊔ c3 = ⊤ := by
  have h02 : b3 0 2 := mergePair_rel (⊥ : Setoid (Fin 3)) 0 2
  have h12 : c3 1 2 := mergePair_rel (⊥ : Setoid (Fin 3)) 1 2
  have h02' : (b3 ⊔ c3) 0 2 := Setoid.le_def.mp le_sup_left h02
  have h12' : (b3 ⊔ c3) 1 2 := Setoid.le_def.mp le_sup_right h12
  have h21' : (b3 ⊔ c3) 2 1 := (b3 ⊔ c3).symm' h12'
  have h01' : (b3 ⊔ c3) 0 1 := (b3 ⊔ c3).trans' h02' h21'
  have h20' : (b3 ⊔ c3) 2 0 := (b3 ⊔ c3).symm' h02'
  have h10' : (b3 ⊔ c3) 1 0 := (b3 ⊔ c3).symm' h01'
  rw [Setoid.eq_top_iff]
  intro x y
  fin_cases x <;> fin_cases y <;>
    first | exact (b3 ⊔ c3).refl' _ | exact h02' | exact h12' | exact h21' | exact h01' | exact h20' | exact h10'

/-- Deza–Laurent, "Geometry of Cuts and Metrics": the pentagonal inequality
holds in every `ℓ1`-embeddable metric space (`ℓ1 ⇒ hypermetric ⇒ 5-gonal`).
The partition metric space on three points already violates it — its
covering graph on `{⊥, a3, b3, c3, ⊤}` is `K_{2,3}`, the standard
non-`ℓ1`, non-partial-cube graph. Hence `shannonDist` does not embed
isometrically in any hypercube/`ℓ1` space; combined with `median_not_unique`
below, Delsol's convex-envelope geometry (their §4) is genuinely
non-Euclidean/non-`ℓ1` even in this finite counting shadow. -/
theorem pentagonal_violation :
    ∃ x1 x2 y1 y2 y3 : Setoid (Fin 3),
      shannonDist y1 y2 + shannonDist y1 y3 + shannonDist y2 y3 + shannonDist x1 x2 >
      shannonDist x1 y1 + shannonDist x1 y2 + shannonDist x1 y3 +
      shannonDist x2 y1 + shannonDist x2 y2 + shannonDist x2 y3 := by
  refine ⟨⊥, ⊤, a3, b3, c3, ?_⟩
  have hab := shannonDist_add_rank_add_rank a3 b3
  have hac := shannonDist_add_rank_add_rank a3 c3
  have hbc := shannonDist_add_rank_add_rank b3 c3
  rw [a3_sup_b3] at hab
  rw [a3_sup_c3] at hac
  rw [b3_sup_c3] at hbc
  have hbotP := shannonDist_bot a3
  have hbotQ := shannonDist_bot b3
  have hbotR := shannonDist_bot c3
  have hbotTop := shannonDist_bot (⊤ : Setoid (Fin 3))
  have htopP := shannonDist_top a3
  have htopQ := shannonDist_top b3
  have htopR := shannonDist_top c3
  have hra := rank_a3
  have hrb := rank_b3
  have hrc := rank_c3
  have hcard : Fintype.card (Fin 3) = 3 := Fintype.card_fin 3
  have hrtop : rank (⊤ : Setoid (Fin 3)) = Fintype.card (Fin 3) - 1 := rank_top
  omega

/-- In a median space the median of any triple is metrically unique. Here
`⊥` and `⊤` are BOTH metrically between every pair of the three atoms
`a3, b3, c3` for `shannonDist`, so the partition metric space on `Fin 3` is
not median. Together with `pentagonal_violation` this pins down the
geometry: `shannonDist` is a submodular-rank (upper-semimodular-lattice)
metric, bipartite (`shannonDist_add_rank_add_rank`), but not cubical
(Delsol et al. 2024, §4; Deza–Laurent). -/
theorem median_not_unique :
    ∃ a b c m₁ m₂ : Setoid (Fin 3), m₁ ≠ m₂ ∧
      (shannonDist a m₁ + shannonDist m₁ b = shannonDist a b) ∧
      (shannonDist b m₁ + shannonDist m₁ c = shannonDist b c) ∧
      (shannonDist a m₁ + shannonDist m₁ c = shannonDist a c) ∧
      (shannonDist a m₂ + shannonDist m₂ b = shannonDist a b) ∧
      (shannonDist b m₂ + shannonDist m₂ c = shannonDist b c) ∧
      (shannonDist a m₂ + shannonDist m₂ c = shannonDist a c) := by
  have hab := shannonDist_add_rank_add_rank a3 b3
  have hac := shannonDist_add_rank_add_rank a3 c3
  have hbc := shannonDist_add_rank_add_rank b3 c3
  rw [a3_sup_b3] at hab
  rw [a3_sup_c3] at hac
  rw [b3_sup_c3] at hbc
  have hbotP := shannonDist_bot a3
  have hbotQ := shannonDist_bot b3
  have hbotR := shannonDist_bot c3
  have htopP := shannonDist_top a3
  have htopQ := shannonDist_top b3
  have htopR := shannonDist_top c3
  have hcommPbot := shannonDist_comm a3 (⊥ : Setoid (Fin 3))
  have hcommQbot := shannonDist_comm b3 (⊥ : Setoid (Fin 3))
  have hcommRbot := shannonDist_comm c3 (⊥ : Setoid (Fin 3))
  have hcommPtop := shannonDist_comm a3 (⊤ : Setoid (Fin 3))
  have hcommQtop := shannonDist_comm b3 (⊤ : Setoid (Fin 3))
  have hcommRtop := shannonDist_comm c3 (⊤ : Setoid (Fin 3))
  have hra := rank_a3
  have hrb := rank_b3
  have hrc := rank_c3
  have hcard : Fintype.card (Fin 3) = 3 := Fintype.card_fin 3
  have hrtop : rank (⊤ : Setoid (Fin 3)) = Fintype.card (Fin 3) - 1 := rank_top
  have hbcbot : blockCount (⊥ : Setoid (Fin 3)) = 3 := by rw [blockCount_bot, Fintype.card_fin]
  have hbctop : blockCount (⊤ : Setoid (Fin 3)) = 1 := blockCount_top
  have hne : (⊥ : Setoid (Fin 3)) ≠ ⊤ := by
    intro h
    rw [h] at hbcbot
    omega
  refine ⟨a3, b3, c3, ⊥, ⊤, hne, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
