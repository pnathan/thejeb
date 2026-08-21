/-
Stuck states of the GYO (Graham) reduction — the structural half of the
converse BFMY direction.

`Ste.AcyclicSolvability` proves GYO-reducible schemes solvable from
pairwise consistency; `Ste.AcyclicConverse` refutes the converse on the
cyclic family.  Closing the *general* converse needs `¬ GYOReducible E`
turned into a combinatorial object one can plant a parity gadget on.
This file is the first half of that bridge: **stuck states** `(S, K)` —
live vertices remain, but neither an ear step (`NoEar`) nor a
contraction step (`NoContract`) applies.  `not_gyo_of_stuck`: such a
state admits no derivation.  `exists_stuck_of_not_gyoReducible`: greedy
reduction from the full state strictly drops `S.card + K.card` at every
step, so it halts — at a stuck state.  The remaining theorems are the
payload consumed by a later walk-extraction stage: every covered live
vertex lies in at least two live edges, the live traces form an
antichain, and distinct live edges have private live vertices.  There is
no `sorry` in this file.

References: Beeri–Fagin–Maier–Yannakakis, *On the desirability of acyclic
database schemes*, JACM 30(3):479–513, 1983 (`beeri1983acyclic`); Fagin,
*Degrees of acyclicity for hypergraphs and relational database schemes*,
JACM 30(3):514–550, 1983 (`fagin1983degrees`).
-/
import Ste.AcyclicSolvability

namespace STE

/-! ### Stuck states -/

/-- **No ear**: no live vertex lies in exactly one live edge.  This is
the exact negation of the hypothesis bundle of `GYO.ear`. -/
def NoEar {m n : ℕ} (E : Fin m → Finset (Fin (n + 1)))
    (S : Finset (Fin (n + 1))) (K : Finset (Fin m)) : Prop :=
  ∀ v ∈ S, ∀ k₀ ∈ K, v ∈ E k₀ → ¬ (∀ k ∈ K, v ∈ E k → k = k₀)

/-- **No contraction**: no live edge's live trace `E k ∩ S` is contained
in that of another live edge.  This is the exact negation of the side
condition of `GYO.contract`. -/
def NoContract {m n : ℕ} (E : Fin m → Finset (Fin (n + 1)))
    (S : Finset (Fin (n + 1))) (K : Finset (Fin m)) : Prop :=
  ∀ k ∈ K, ∀ k' ∈ K, k' ≠ k → ¬ (E k ∩ S ⊆ E k' ∩ S)

/-- **A stuck state**: live vertices remain, but neither GYO step
applies. -/
def Stuck {m n : ℕ} (E : Fin m → Finset (Fin (n + 1)))
    (S : Finset (Fin (n + 1))) (K : Finset (Fin m)) : Prop :=
  S.Nonempty ∧ NoEar E S K ∧ NoContract E S K

/-! ### A stuck state admits no derivation -/

/-- **No derivation from a stuck state.**  Inverting on the first step of
a putative derivation (as `gyo_first_step` does) yields either an ear or
a contraction, each contradicting one half of `Stuck`; the `empty`
constructor contradicts `S.Nonempty`. -/
theorem not_gyo_of_stuck {m n : ℕ} {E : Fin m → Finset (Fin (n + 1))}
    {S : Finset (Fin (n + 1))} {K : Finset (Fin m)}
    (hst : Stuck E S K) : ¬ GYO E S K := by
  obtain ⟨hS, hear, hcon⟩ := hst
  intro h
  cases h with
  | empty K => exact absurd hS Finset.not_nonempty_empty
  | ear hv hk₀ hvk₀ honly _ => exact hear _ hv _ hk₀ hvk₀ honly
  | contract hk hk' hne hsub _ => exact hcon _ hk _ hk' hne hsub

/-! ### The greedy reduction halts at a stuck state -/

/-- **Greedy reduction, bounded form.**  If no state is stuck, then every
state with `S.card + K.card ≤ N` is GYO-reducible.  Induction on `N`: a
nonempty non-stuck state admits an ear step (which strictly drops
`S.card`) or a contraction step (which strictly drops `K.card`), and in
either case the successor hypothesis supplies the sub-derivation. -/
theorem gyo_of_card_le_of_forall_not_stuck {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} (h : ∀ S K, ¬ Stuck E S K) :
    ∀ (N : ℕ) (S : Finset (Fin (n + 1))) (K : Finset (Fin m)),
      S.card + K.card ≤ N → GYO E S K := by
  intro N
  induction N with
  | zero =>
    intro S K hle
    have : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst this
    exact GYO.empty K
  | succ N ih =>
    intro S K hle
    rcases S.eq_empty_or_nonempty with rfl | hS
    · exact GYO.empty K
    · have hnot : ¬ (NoEar E S K ∧ NoContract E S K) :=
        fun hc => h S K ⟨hS, hc.1, hc.2⟩
      rcases not_and_or.mp hnot with hne | hnc
      · rw [NoEar] at hne
        push Not at hne
        obtain ⟨v, hv, k₀, hk₀, hvk₀, honly⟩ := hne
        refine GYO.ear hv hk₀ hvk₀ honly (ih _ _ ?_)
        have hcard : (S.erase v).card = S.card - 1 := Finset.card_erase_of_mem hv
        have hpos : 0 < S.card := Finset.card_pos.mpr ⟨v, hv⟩
        omega
      · rw [NoContract] at hnc
        push Not at hnc
        obtain ⟨k, hk, k', hk', hkk', hsub⟩ := hnc
        refine GYO.contract hk hk' hkk' hsub (ih _ _ ?_)
        have hcard : (K.erase k).card = K.card - 1 := Finset.card_erase_of_mem hk
        have hpos : 0 < K.card := Finset.card_pos.mpr ⟨k, hk⟩
        omega

/-- **No stuck state ⇒ GYO-reducible.**  The contrapositive form of the
existence lemma: the greedy reduction from the full state runs to
completion. -/
theorem gyoReducible_of_forall_not_stuck {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} (h : ∀ S K, ¬ Stuck E S K) :
    GYOReducible E :=
  gyo_of_card_le_of_forall_not_stuck h _ Finset.univ Finset.univ le_rfl

/-- **The key existence lemma.**  A hypergraph that is not GYO-reducible
has a stuck state: greedily reducing from the full state strictly drops
the measure `S.card + K.card` at every step, so it halts, and it cannot
halt at `S = ∅` (that would be a derivation).  This is the structural
witness of non-α-acyclicity that the walk-extraction stage consumes. -/
theorem exists_stuck_of_not_gyoReducible {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} (h : ¬ GYOReducible E) :
    ∃ (S : Finset (Fin (n + 1))) (K : Finset (Fin m)), Stuck E S K := by
  by_contra hc
  push Not at hc
  exact h (gyoReducible_of_forall_not_stuck hc)

/-! ### Structural consequences of stuckness -/

/-- **At least two live edges through every covered live vertex.**  The
ear constructor asks for a live vertex lying in *exactly one* live edge,
so `NoEar` says every live vertex lies in zero or at least two.  The
covering hypothesis — stated honestly as the parameters `hk₀ : k₀ ∈ K`
and `hvk₀ : v ∈ E k₀`, i.e. `v` is covered by *some* live edge — rules
out zero and leaves "at least two". -/
theorem two_live_edges_of_stuck {m n : ℕ} {E : Fin m → Finset (Fin (n + 1))}
    {S : Finset (Fin (n + 1))} {K : Finset (Fin m)} (hst : Stuck E S K)
    {v : Fin (n + 1)} (hv : v ∈ S) {k₀ : Fin m} (hk₀ : k₀ ∈ K)
    (hvk₀ : v ∈ E k₀) :
    ∃ k₁ ∈ K, v ∈ E k₁ ∧ k₁ ≠ k₀ := by
  have hne := hst.2.1 v hv k₀ hk₀ hvk₀
  push Not at hne
  exact hne

/-- **The live traces form an antichain.**  Direct restatement of
`NoContract`: at a stuck state no live edge's live trace `E k ∩ S` is
contained in another live edge's live trace. -/
theorem live_traces_antichain_of_stuck {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} {S : Finset (Fin (n + 1))}
    {K : Finset (Fin m)} (hst : Stuck E S K) :
    ∀ k ∈ K, ∀ k' ∈ K, k ≠ k' → ¬ (E k ∩ S ⊆ E k' ∩ S) :=
  fun k hk k' hk' hne => hst.2.2 k hk k' hk' (Ne.symm hne)

/-- **Private live vertices.**  Immediate corollary of the antichain
lemma: for any two distinct live edges `k ≠ k'` there is a live vertex of
`k` outside `k'`.  This is the local freedom the walk-extraction stage
walks on — from any live edge one can always step to a vertex the
neighbouring edge does not see. -/
theorem exists_private_vertex_of_stuck {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} {S : Finset (Fin (n + 1))}
    {K : Finset (Fin m)} (hst : Stuck E S K) {k k' : Fin m}
    (hk : k ∈ K) (hk' : k' ∈ K) (hne : k ≠ k') :
    ∃ v ∈ S, v ∈ E k ∧ v ∉ E k' := by
  have hsub := live_traces_antichain_of_stuck hst k hk k' hk' hne
  rw [Finset.subset_iff] at hsub
  push Not at hsub
  obtain ⟨v, hvk, hvk'⟩ := hsub
  rw [Finset.mem_inter] at hvk
  rw [Finset.mem_inter] at hvk'
  exact ⟨v, hvk.2, hvk.1, fun hc => hvk' ⟨hc, hvk.2⟩⟩
