/-
The full converse BFMY direction: gadgets planted on the combinatorial
obstructions to α-acyclicity.

`Ste.AcyclicSolvability` proves the forward BFMY implication
(`gyoReducible_pairwiseConsistent_solvable`); `Ste.AcyclicConverse`
refutes the converse on the cyclic family only; `Ste.StuckState` turns
`¬ GYOReducible E` into a *stuck state* of the GYO reduction.  This file
carries the general converse: the two gadgets, the extraction machinery,
and their composition.

**What is mechanized (no `sorry`).**

1. **The parity gadget on a chord-free cycle.**  `BFMYCycle E v` — an
   injective cyclic sequence of length `≥ 3` whose consecutive pairs are
   each covered by a hyperedge and *no hyperedge sees two of those pairs*
   (`chordfree`) — carries `cycRel`, edge-supported
   (`cycRel_edgeSupported`), pairwise consistent
   (`cycRel_pairwiseConsistent`), with every table nonempty
   (`cycRel_tables_nonempty`) and no global solution
   (`cycRel_not_solvable`), over the concrete alphabet `ℕ` with full
   domains.  Packaged as `bfmyCycle_pairwiseConsistent_not_solvable`.
   `chordfree` is exactly what pairwise consistency needs: it makes each
   hyperedge carry at most one XOR constraint.
2. **The colouring gadget on an uncovered clique.**  `UncoveredClique
   E C` — every pair of `C` covered, `C` itself covered by no hyperedge,
   `3 ≤ C.card`.  `cliqRel` demands that each hyperedge colour the part
   of `C` it sees injectively with colours `< C.card - 1`.  Locally
   satisfiable (a hyperedge misses a vertex of `C`, so it sees at most
   `C.card - 1` of them — `cliq_slice_card`), pairwise consistent by
   greedy re-colouring outside the other hyperedge
   (`exists_colouring_extend`), globally impossible (the clique forces
   `C.card` distinct colours).  Packaged as
   `uncoveredClique_pairwiseConsistent_not_solvable`.  The parity gadget
   does *not* cover this case: on `{123,124,134,234}` the parity system
   is nonsingular over `GF(2)` and always solvable.
3. **Non-conformality is immediately an uncovered clique**
   (`exists_uncoveredClique_of_not_conformal`), and a chordless cycle of
   length `≥ 4` is immediately a BFMY cycle
   (`exists_bfmyCycle_of_not_chordal`).  So
   `not_conformal_or_not_chordal_pairwiseConsistent_not_solvable`:
   failure of either classical acyclicity ingredient already produces the
   counterexample instance — unconditionally.
4. **Reachable stuck states.**  `Stuck` alone is vacuous (`Stuck E S ∅`
   holds for every nonempty `S`), so this file strengthens it to
   `StuckReduced`, adding the invariant the greedy reduction actually
   maintains — every dead edge's live trace is dominated by a live one —
   and re-proves the halting argument with it
   (`exists_stuckReduced_of_not_gyoReducible`).  Consequences:
   `not_simplicial_of_stuckReduced` (no live vertex has its closed live
   neighbourhood inside one live edge), and, under conformality,
   `exists_nonadjacent_neighbours_of_stuckReduced` (**no vertex of `S` is
   simplicial in the primal graph**).  Live obstructions lift to `E`:
   `bfmyCycle_of_live`, `uncoveredClique_of_live`,
   `primalAdj_live_of_stuckReduced`.
5. **Composition.**  `extraction_of_dirac`,
   `not_gyoReducible_exists_pairwiseConsistent_not_solvable` and the
   biconditional `gyoReducible_iff_pairwiseConsistent_solvable_of_dirac`,
   each taking `DiracHypothesis E` as an explicit hypothesis.

**The honest residue.**  `DiracHypothesis` — Dirac's simplicial-vertex
theorem for the primal graph: a finite induced subgraph with no
simplicial vertex contains a chordless cycle of length `≥ 4`.  It is a
purely graph-theoretic statement, independent of everything else here,
and it is *not* proved in this file; it is the single gap between item 4
(no simplicial vertex at a reachable stuck state) and item 3 (a chordless
cycle gives the gadget).  It is stated as a `def` and threaded explicitly
through the theorems that need it, so nothing is smuggled.  The covering
hypothesis `∀ v, ∃ k, v ∈ E k` appears where it is genuinely needed: it
rules out a vertex in no hyperedge, which is an "uncovered set" of size
one on which no gadget can say anything.

There is no `sorry` in this file.

References: Beeri–Fagin–Maier–Yannakakis, *On the desirability of acyclic
database schemes*, JACM 30(3):479–513, 1983 (`beeri1983acyclic`); Fagin,
*Degrees of acyclicity for hypergraphs and relational database schemes*,
JACM 30(3):514–550, 1983 (`fagin1983degrees`); G. A. Dirac, *On rigid
circuit graphs*, Abh. Math. Sem. Univ. Hamburg 25:71–76, 1961.
-/
import Mathlib.Tactic.Abel
import Ste.AcyclicConverse
import Ste.StuckState

namespace STE

open Set

/-! ### Chordless cycles of a hypergraph

A **BFMY cycle** of length `p + 3` is a cyclically indexed injective
sequence of vertices `v : Fin (p + 3) → Fin (n + 1)` such that

* every *consecutive* pair `{v (i-1), v i}` lies in a common hyperedge
  (`cover`), and
* **no hyperedge sees two different consecutive pairs** (`chordfree`):
  if `E k` contains both `v (i-1), v i` and `v (j-1), v j` then `i = j`.

For length `≥ 4` `chordfree` is the usual chordlessness of the cycle in
the primal graph (a chord `{v p, v q}` between non-consecutive vertices
would be a hyperedge seeing two consecutive pairs); for length `3` it is
the statement that no single hyperedge covers the triangle, i.e. that
the triangle is a *conformality* violation.  Both are the classical
"weak β-cycle" obstruction of `fagin1983degrees`. -/
structure BFMYCycle {m n p : ℕ} (E : Fin m → Finset (Fin (n + 1)))
    (v : Fin (p + 3) → Fin (n + 1)) : Prop where
  /-- The cycle visits `p + 3` distinct vertices. -/
  inj : Function.Injective v
  /-- Consecutive vertices share a hyperedge. -/
  cover : ∀ i, ∃ k, v (i - 1) ∈ E k ∧ v i ∈ E k
  /-- No hyperedge sees two distinct consecutive pairs. -/
  chordfree : ∀ (k : Fin m) (i j : Fin (p + 3)),
      v (i - 1) ∈ E k → v i ∈ E k → v (j - 1) ∈ E k → v j ∈ E k → i = j

/-- On `Fin (p + 3)` the predecessor of an index is never the index
itself: `1 ≠ 0` in this nontrivial commutative ring. -/
theorem sub_one_ne_self {p : ℕ} (i : Fin (p + 3)) : i - 1 ≠ i := by
  intro h
  have h1 : (1 : Fin (p + 3)) = 0 := by
    have := sub_eq_self.mp h
    exact this
  have : ((1 : Fin (p + 3)) : ℕ) = ((0 : Fin (p + 3)) : ℕ) := congrArg Fin.val h1
  simp [Nat.mod_eq_of_lt] at this

/-! ### The parity gadget on a BFMY cycle

Alphabet `ℕ`, domains `Set.univ`.  Hyperedge `k` carries the constraint
"for every consecutive pair `{v (i-1), v i}` that `E k` happens to
contain, the two values have parity `par i`", where `par` is odd
overall — exactly one index (`0`) is twisted.  `chordfree` says at most
one index is active for each hyperedge, so the constraint is really a
single XOR when it constrains anything at all, and is vacuous for every
hyperedge missing the cycle. -/

/-- The frustrated parameter: total parity `1` around the cycle. -/
def par {p : ℕ} : Fin (p + 3) → ℕ := fun i => if i = 0 then 1 else 0

theorem par_lt_two {p : ℕ} (i : Fin (p + 3)) : par i < 2 := by
  unfold par; split <;> omega

theorem sum_par {p : ℕ} : ∑ i : Fin (p + 3), par i = 1 := by
  simp [par, Finset.sum_ite_eq' Finset.univ (0 : Fin (p + 3)) (fun _ => 1)]

/-- **The cycle relation**: hyperedge `k` constrains the parity of every
consecutive cycle pair it contains. -/
def cycRel {m n p : ℕ} (E : Fin m → Finset (Fin (n + 1)))
    (v : Fin (p + 3) → Fin (n + 1)) : Fin m → (Fin (n + 1) → ℕ) → Prop :=
  fun k g => ∀ i : Fin (p + 3), v (i - 1) ∈ E k → v i ∈ E k →
    (g (v (i - 1)) + g (v i)) % 2 = par i

/-- The cycle relation has edge scope: each conjunct is guarded by
membership of both its vertices in `E k`. -/
theorem cycRel_edgeSupported {m n p : ℕ} (E : Fin m → Finset (Fin (n + 1)))
    (v : Fin (p + 3) → Fin (n + 1)) : EdgeSupported E (cycRel E v) := by
  intro k g g' hag
  constructor <;> intro h i h1 h2
  · rw [← hag _ h1, ← hag _ h2]; exact h i h1 h2
  · rw [hag _ h1, hag _ h2]; exact h i h1 h2

/-- Consecutive cycle vertices are distinct. -/
theorem cyc_ne {m n p : ℕ} {E : Fin m → Finset (Fin (n + 1))}
    {v : Fin (p + 3) → Fin (n + 1)} (hc : BFMYCycle E v) (i : Fin (p + 3)) :
    v (i - 1) ≠ v i := fun h => sub_one_ne_self i (hc.inj h)

/-- **Every table is nonempty.**  `chordfree` leaves at most one active
index per hyperedge, so a single value placed at that index's head
vertex satisfies the whole constraint. -/
theorem cycRel_tables_nonempty {m n p : ℕ} {E : Fin m → Finset (Fin (n + 1))}
    {v : Fin (p + 3) → Fin (n + 1)} (hc : BFMYCycle E v) (k : Fin m) :
    ∃ t : Fin (n + 1) → ℕ,
      (∀ u, t u ∈ (Set.univ : Set ℕ)) ∧ cycRel E v k t := by
  by_cases hex : ∃ i : Fin (p + 3), v (i - 1) ∈ E k ∧ v i ∈ E k
  · obtain ⟨i₀, h1₀, h2₀⟩ := hex
    refine ⟨fun u => if u = v i₀ then par i₀ else 0, fun _ => trivial, ?_⟩
    intro i h1 h2
    have hi : i = i₀ := hc.chordfree k i i₀ h1 h2 h1₀ h2₀
    subst hi
    show ((if v (i - 1) = v i then par i else 0)
        + (if v i = v i then par i else 0)) % 2 = par i
    rw [if_neg (cyc_ne hc i), if_pos rfl]
    simpa using Nat.mod_eq_of_lt (par_lt_two i)
  · exact ⟨fun _ => 0, fun _ => trivial, fun i h1 h2 => absurd ⟨i, h1, h2⟩ hex⟩

/-- **Pairwise consistency of the cycle gadget.**  Given a tuple of
hyperedge `k`, the only constraint of hyperedge `k'` is its unique active
index `i` (if any).  Either `E k` also contains both `v (i-1)` and `v i`
— then `i` is active for `k` too and the given tuple already satisfies
the constraint — or one of the two vertices lies outside `E k`, and
re-assigning it (a change invisible on `E k ∩ E k'`) repairs the parity.
This is where `chordfree` does its work: without it two active indices of
`k'` could impose contradictory demands on a tuple of `k`. -/
theorem cycRel_pairwiseConsistent {m n p : ℕ} {E : Fin m → Finset (Fin (n + 1))}
    {v : Fin (p + 3) → Fin (n + 1)} (hc : BFMYCycle E v) :
    PairwiseConsistent (fun _ => (Set.univ : Set ℕ)) E (cycRel E v) := by
  intro k k' g _ hgk
  by_cases hex : ∃ i : Fin (p + 3), v (i - 1) ∈ E k' ∧ v i ∈ E k'
  · obtain ⟨i, h1', h2'⟩ := hex
    have hpar := par_lt_two i
    have hne := cyc_ne hc i
    by_cases hb1 : v (i - 1) ∈ E k
    · by_cases hb2 : v i ∈ E k
      · refine ⟨g, fun _ => trivial, ?_, fun _ _ => rfl⟩
        intro j hj1 hj2
        have hji : j = i := hc.chordfree k' j i hj1 hj2 h1' h2'
        subst j
        exact hgk i hb1 hb2
      · refine ⟨Function.update g (v i) (par i + g (v (i - 1))),
          fun _ => trivial, ?_, ?_⟩
        · intro j hj1 hj2
          have hji : j = i := hc.chordfree k' j i hj1 hj2 h1' h2'
          subst j
          rw [Function.update_of_ne hne, Function.update_self]
          omega
        · intro u hu
          refine Function.update_of_ne (fun h => hb2 ?_) _ _
          rw [← h]
          exact (Finset.mem_inter.mp hu).1
    · refine ⟨Function.update g (v (i - 1)) (par i + g (v i)),
        fun _ => trivial, ?_, ?_⟩
      · intro j hj1 hj2
        have hji : j = i := hc.chordfree k' j i hj1 hj2 h1' h2'
        subst j
        rw [Function.update_self, Function.update_of_ne (Ne.symm hne)]
        omega
      · intro u hu
        refine Function.update_of_ne (fun h => hb1 ?_) _ _
        rw [← h]
        exact (Finset.mem_inter.mp hu).1
  · exact ⟨g, fun _ => trivial, fun i h1 h2 => absurd ⟨i, h1, h2⟩ hex,
      fun _ _ => rfl⟩

/-- **The frustrated cycle has no global solution.**  Each consecutive
pair is covered by some hyperedge (`cover`), so a global tuple would have
to satisfy *every* parity constraint; summing them around the cycle each
vertex value occurs exactly twice, so the total is even, contradicting
the odd total parity `∑ par = 1`. -/
theorem cycRel_not_solvable {m n p : ℕ} {E : Fin m → Finset (Fin (n + 1))}
    {v : Fin (p + 3) → Fin (n + 1)} (hc : BFMYCycle E v) :
    ¬ ∃ f : Fin (n + 1) → ℕ,
      (∀ u, f u ∈ (Set.univ : Set ℕ)) ∧ ∀ k, cycRel E v k f := by
  rintro ⟨f, -, hf⟩
  have hstep : ∀ i : Fin (p + 3),
      (f (v (i - 1)) + f (v i)) % 2 = par i := by
    intro i
    obtain ⟨k, h1, h2⟩ := hc.cover i
    exact hf k i h1 h2
  have hshift : ∑ i : Fin (p + 3), f (v (i - 1)) = ∑ i : Fin (p + 3), f (v i) :=
    Fintype.sum_equiv (Equiv.subRight (1 : Fin (p + 3))) _ _ fun _ => rfl
  have hsum : (∑ i : Fin (p + 3), (f (v (i - 1)) + f (v i))) % 2 = 1 := by
    rw [Finset.sum_nat_mod]
    simp only [hstep]
    rw [sum_par]
  rw [Finset.sum_add_distrib, hshift, ← two_mul] at hsum
  omega

/-! ### The converse witness on a BFMY cycle -/

/-- **The gadget theorem.**  A hypergraph carrying a BFMY cycle supports
edge-supported, pairwise-consistent, locally nonempty relations with no
global solution — over the concrete alphabet `ℕ` with full domains.  This
is the "plant the parity gadget on a weak β-cycle" half of the converse
BFMY direction, in the form the extraction stage feeds. -/
theorem bfmyCycle_pairwiseConsistent_not_solvable {m n p : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} {v : Fin (p + 3) → Fin (n + 1)}
    (hc : BFMYCycle E v) :
    ∃ Rel : Fin m → (Fin (n + 1) → ℕ) → Prop,
      EdgeSupported E Rel ∧
      PairwiseConsistent (fun _ => (Set.univ : Set ℕ)) E Rel ∧
      (∀ k, ∃ t : Fin (n + 1) → ℕ,
        (∀ u, t u ∈ (Set.univ : Set ℕ)) ∧ Rel k t) ∧
      ¬ ∃ f : Fin (n + 1) → ℕ,
        (∀ u, f u ∈ (Set.univ : Set ℕ)) ∧ ∀ k, Rel k f :=
  ⟨cycRel E v, cycRel_edgeSupported E v, cycRel_pairwiseConsistent hc,
    cycRel_tables_nonempty hc, cycRel_not_solvable hc⟩

/-! ### Uncovered cliques: the conformality obstruction

The second obstruction to α-acyclicity is failure of *conformality*: a
set `C` of vertices that is a clique of the primal graph (every pair
lies in a common hyperedge) but that no single hyperedge contains.  The
BFMY cycle above is the `C.card = 3` case only when no hyperedge covers
the triangle; for larger `C` a hyperedge may well cover any three of its
vertices, and the parity gadget then becomes solvable.  The gadget that
does work for arbitrary `C` is *injectivity with too few colours*: every
hyperedge demands that its slice of `C` receive distinct colours drawn
from `C.card - 1` of them.  Locally there are enough colours (a hyperedge
sees at most `C.card - 1` vertices of `C`, precisely because `C` is
uncovered); globally there are not (the clique forces all `C.card`
vertices to differ). -/

/-- **An uncovered clique**: every pair of `C` shares a hyperedge, but no
hyperedge contains all of `C`.  `card` is recorded as a field; it is
automatic whenever every vertex lies in some hyperedge, since an
uncovered set of size `≤ 2` would contradict `pairs` (size 2) or the
covering hypothesis (size `≤ 1`). -/
structure UncoveredClique {m n : ℕ} (E : Fin m → Finset (Fin (n + 1)))
    (C : Finset (Fin (n + 1))) : Prop where
  /-- Every two distinct vertices of `C` lie in a common hyperedge. -/
  pairs : ∀ u ∈ C, ∀ w ∈ C, u ≠ w → ∃ k, u ∈ E k ∧ w ∈ E k
  /-- No hyperedge contains all of `C`. -/
  uncovered : ∀ k, ¬ C ⊆ E k
  /-- `C` has at least three vertices. -/
  card : 3 ≤ C.card

/-- **The colouring relation**: hyperedge `k` demands that the vertices
of `C` it sees carry distinct colours below `C.card - 1`. -/
def cliqRel {m n : ℕ} (E : Fin m → Finset (Fin (n + 1)))
    (C : Finset (Fin (n + 1))) : Fin m → (Fin (n + 1) → ℕ) → Prop :=
  fun k g => (∀ u ∈ C ∩ E k, ∀ w ∈ C ∩ E k, g u = g w → u = w) ∧
    (∀ u ∈ C ∩ E k, g u < C.card - 1)

theorem cliqRel_edgeSupported {m n : ℕ} (E : Fin m → Finset (Fin (n + 1)))
    (C : Finset (Fin (n + 1))) : EdgeSupported E (cliqRel E C) := by
  intro k g g' hag
  have key : ∀ u ∈ C ∩ E k, g u = g' u :=
    fun u hu => hag u (Finset.mem_inter.mp hu).2
  constructor
  · rintro ⟨hinj, hlt⟩
    exact ⟨fun u hu w hw h => hinj u hu w hw (by rw [key u hu, key w hw, h]),
      fun u hu => (key u hu) ▸ hlt u hu⟩
  · rintro ⟨hinj, hlt⟩
    exact ⟨fun u hu w hw h => hinj u hu w hw (by rw [← key u hu, ← key w hw, h]),
      fun u hu => (key u hu).symm ▸ hlt u hu⟩

/-- A hyperedge sees at most `C.card - 1` vertices of an uncovered
clique — it misses at least one. -/
theorem cliq_slice_card {m n : ℕ} {E : Fin m → Finset (Fin (n + 1))}
    {C : Finset (Fin (n + 1))} (hC : UncoveredClique E C) (k : Fin m) :
    (C ∩ E k).card ≤ C.card - 1 := by
  obtain ⟨u, huC, huk⟩ := Finset.not_subset.mp (hC.uncovered k)
  have hsub : C ∩ E k ⊆ C.erase u := by
    intro w hw
    rw [Finset.mem_inter] at hw
    exact Finset.mem_erase.mpr ⟨fun h => huk (h ▸ hw.2), hw.1⟩
  calc (C ∩ E k).card ≤ (C.erase u).card := Finset.card_le_card hsub
    _ = C.card - 1 := Finset.card_erase_of_mem huC

/-- **Greedy colour extension.**  A partial colouring of `A ⊆ s`, proper
and with colours below `N`, extends to a proper colouring of the whole of
`s` with colours below `N`, provided `s.card ≤ N`.  Induction on the
number of uncoloured vertices: at each step at most `s.card - 1 < N`
colours are used, so a fresh one is available.  This is the local half of
the conformality gadget. -/
theorem exists_colouring_extend {ι : Type*} [DecidableEq ι] (N : ℕ) :
    ∀ (d : ℕ) (s A : Finset ι) (f : ι → ℕ), (s \ A).card = d → A ⊆ s →
      (∀ u ∈ A, ∀ w ∈ A, f u = f w → u = w) → (∀ u ∈ A, f u < N) →
      s.card ≤ N →
      ∃ g : ι → ℕ, (∀ u ∈ A, g u = f u) ∧
        (∀ u ∈ s, ∀ w ∈ s, g u = g w → u = w) ∧ (∀ u ∈ s, g u < N) := by
  intro d
  induction d with
  | zero =>
    intro s A f hd hAs hinj hlt _
    have hsub : s ⊆ A := by
      intro u hu
      by_contra h
      exact absurd (Finset.card_eq_zero.mp hd)
        (Finset.ne_empty_of_mem (Finset.mem_sdiff.mpr ⟨hu, h⟩))
    exact ⟨f, fun _ _ => rfl, fun u hu w hw h => hinj u (hsub hu) w (hsub hw) h,
      fun u hu => hlt u (hsub hu)⟩
  | succ d ih =>
    intro s A f hd hAs hinj hlt hcard
    obtain ⟨x, hx⟩ : (s \ A).Nonempty := Finset.card_pos.mp (by omega)
    rw [Finset.mem_sdiff] at hx
    have hne : ∀ u ∈ A, u ≠ x := fun u hu h => hx.2 (by rwa [h] at hu)
    have hAcard : A.card ≤ s.card - 1 := by
      have : A ⊆ s.erase x := fun u hu =>
        Finset.mem_erase.mpr ⟨fun h => hx.2 (h ▸ hu), hAs hu⟩
      calc A.card ≤ (s.erase x).card := Finset.card_le_card this
        _ = s.card - 1 := Finset.card_erase_of_mem hx.1
    have hspos : 0 < s.card := Finset.card_pos.mpr ⟨x, hx.1⟩
    obtain ⟨c, hc⟩ : (Finset.range N \ A.image f).Nonempty := by
      rw [← Finset.card_pos]
      have h1 : (A.image f).card ≤ A.card := Finset.card_image_le
      have h2 := Finset.le_card_sdiff (A.image f) (Finset.range N)
      rw [Finset.card_range] at h2
      omega
    rw [Finset.mem_sdiff, Finset.mem_range] at hc
    refine ih s (insert x A) (Function.update f x c) ?_ ?_ ?_ ?_ hcard |>.imp
      fun g hg => ⟨fun u hu => ?_, hg.2.1, hg.2.2⟩
    · rw [Finset.sdiff_insert, Finset.card_erase_of_mem
        (Finset.mem_sdiff.mpr ⟨hx.1, hx.2⟩)]
      omega
    · exact Finset.insert_subset hx.1 hAs
    · intro u hu w hw h
      rcases Finset.mem_insert.mp hu with rfl | hu' <;>
        rcases Finset.mem_insert.mp hw with rfl | hw'
      · rfl
      · rw [Function.update_self, Function.update_of_ne (hne w hw')] at h
        exact absurd (Finset.mem_image.mpr ⟨w, hw', h.symm⟩) hc.2
      · rw [Function.update_self, Function.update_of_ne (hne u hu')] at h
        exact absurd (Finset.mem_image.mpr ⟨u, hu', h⟩) hc.2
      · rw [Function.update_of_ne (hne u hu'),
          Function.update_of_ne (hne w hw')] at h
        exact hinj u hu' w hw' h
    · intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu'
      · rw [Function.update_self]; exact hc.1
      · rw [Function.update_of_ne (hne u hu')]; exact hlt u hu'
    · rw [hg.1 u (Finset.mem_insert_of_mem hu),
        Function.update_of_ne (hne u hu)]


/-- **Every table is nonempty**: a hyperedge sees at most `C.card - 1`
vertices of `C`, so the greedy colouring (starting from nothing) fits. -/
theorem cliqRel_tables_nonempty {m n : ℕ} {E : Fin m → Finset (Fin (n + 1))}
    {C : Finset (Fin (n + 1))} (hC : UncoveredClique E C) (k : Fin m) :
    ∃ t : Fin (n + 1) → ℕ,
      (∀ u, t u ∈ (Set.univ : Set ℕ)) ∧ cliqRel E C k t := by
  obtain ⟨g, -, hinj, hlt⟩ := exists_colouring_extend (C.card - 1)
    (C ∩ E k).card (C ∩ E k) ∅ (fun _ => 0) (by simp) (Finset.empty_subset _)
    (by simp) (by simp) (cliq_slice_card hC k)
  exact ⟨g, fun _ => trivial, hinj, hlt⟩

/-- **Pairwise consistency of the conformality gadget.**  The colours the
tuple of `k` already fixes on `C ∩ E k' ∩ E k` are proper and lie below
`C.card - 1`; the greedy extension colours the rest of `C ∩ E k'` — all
of it outside `E k`, hence invisible on `E k ∩ E k'`. -/
theorem cliqRel_pairwiseConsistent {m n : ℕ} {E : Fin m → Finset (Fin (n + 1))}
    {C : Finset (Fin (n + 1))} (hC : UncoveredClique E C) :
    PairwiseConsistent (fun _ => (Set.univ : Set ℕ)) E (cliqRel E C) := by
  intro k k' g _ hgk
  obtain ⟨hinj, hlt⟩ := hgk
  have hAsub : (C ∩ E k') ∩ E k ⊆ C ∩ E k := by
    intro u hu
    rw [Finset.mem_inter] at hu ⊢
    exact ⟨(Finset.mem_inter.mp hu.1).1, hu.2⟩
  obtain ⟨g₀, hg₀A, hg₀inj, hg₀lt⟩ := exists_colouring_extend (C.card - 1)
    ((C ∩ E k') \ ((C ∩ E k') ∩ E k)).card (C ∩ E k') ((C ∩ E k') ∩ E k) g rfl
    Finset.inter_subset_left
    (fun u hu w hw h => hinj u (hAsub hu) w (hAsub hw) h)
    (fun u hu => hlt u (hAsub hu)) (cliq_slice_card hC k')
  classical
  refine ⟨fun u => if u ∈ (C ∩ E k') \ E k then g₀ u else g u,
    fun _ => trivial, ?_, ?_⟩
  · have hval : ∀ u ∈ C ∩ E k',
        (if u ∈ (C ∩ E k') \ E k then g₀ u else g u) = g₀ u := by
      intro u hu
      by_cases hk : u ∈ E k
      · rw [if_neg (by simp [Finset.mem_sdiff, hk])]
        exact (hg₀A u (Finset.mem_inter.mpr ⟨hu, hk⟩)).symm
      · rw [if_pos (Finset.mem_sdiff.mpr ⟨hu, hk⟩)]
    constructor
    · intro u hu w hw h
      have h' : (if u ∈ (C ∩ E k') \ E k then g₀ u else g u)
          = (if w ∈ (C ∩ E k') \ E k then g₀ w else g w) := h
      rw [hval u hu, hval w hw] at h'
      exact hg₀inj u hu w hw h'
    · intro u hu
      show (if u ∈ (C ∩ E k') \ E k then g₀ u else g u) < C.card - 1
      rw [hval u hu]
      exact hg₀lt u hu
  · intro u hu
    refine if_neg ?_
    rw [Finset.mem_sdiff]
    exact fun h => h.2 (Finset.mem_inter.mp hu).1

/-- **The uncovered clique has no global solution.**  Every pair of `C`
lies in a common hyperedge, so a global tuple must colour all `C.card`
vertices of `C` distinctly — with only `C.card - 1` colours available. -/
theorem cliqRel_not_solvable {m n : ℕ} {E : Fin m → Finset (Fin (n + 1))}
    {C : Finset (Fin (n + 1))} (hC : UncoveredClique E C) :
    ¬ ∃ f : Fin (n + 1) → ℕ,
      (∀ u, f u ∈ (Set.univ : Set ℕ)) ∧ ∀ k, cliqRel E C k f := by
  rintro ⟨f, -, hf⟩
  have hcov : ∀ u ∈ C, ∃ k, u ∈ E k := by
    intro u hu
    have hnt : C.Nontrivial :=
      Finset.one_lt_card_iff_nontrivial.mp (by have := hC.card; omega)
    obtain ⟨w, hw, hwu⟩ := hnt.exists_ne u
    obtain ⟨k, h1, -⟩ := hC.pairs u hu w hw (Ne.symm hwu)
    exact ⟨k, h1⟩
  have hinj : Set.InjOn f ↑C := by
    intro u hu w hw h
    by_contra hne
    obtain ⟨k, h1, h2⟩ := hC.pairs u hu w hw hne
    exact hne ((hf k).1 u (Finset.mem_inter.mpr ⟨hu, h1⟩) w
      (Finset.mem_inter.mpr ⟨hw, h2⟩) h)
  have hlt : ∀ u ∈ C, f u < C.card - 1 := by
    intro u hu
    obtain ⟨k, hk⟩ := hcov u hu
    exact (hf k).2 u (Finset.mem_inter.mpr ⟨hu, hk⟩)
  have hcard : (C.image f).card = C.card := Finset.card_image_of_injOn hinj
  have hsub : C.image f ⊆ Finset.range (C.card - 1) := by
    intro c hc
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_range.mpr (hlt u hu)
  have := Finset.card_le_card hsub
  rw [hcard, Finset.card_range] at this
  have := hC.card
  omega

/-- **The conformality gadget theorem.**  A hypergraph carrying an
uncovered clique supports edge-supported, pairwise-consistent, locally
nonempty relations over `ℕ` with no global solution. -/
theorem uncoveredClique_pairwiseConsistent_not_solvable {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} {C : Finset (Fin (n + 1))}
    (hC : UncoveredClique E C) :
    ∃ Rel : Fin m → (Fin (n + 1) → ℕ) → Prop,
      EdgeSupported E Rel ∧
      PairwiseConsistent (fun _ => (Set.univ : Set ℕ)) E Rel ∧
      (∀ k, ∃ t : Fin (n + 1) → ℕ,
        (∀ u, t u ∈ (Set.univ : Set ℕ)) ∧ Rel k t) ∧
      ¬ ∃ f : Fin (n + 1) → ℕ,
        (∀ u, f u ∈ (Set.univ : Set ℕ)) ∧ ∀ k, Rel k f :=
  ⟨cliqRel E C, cliqRel_edgeSupported E C, cliqRel_pairwiseConsistent hC,
    cliqRel_tables_nonempty hC, cliqRel_not_solvable hC⟩

/-! ### Conformality: the first half of the extraction

A hypergraph is **conformal** when every clique of its primal graph — every
set whose pairs are each covered by some hyperedge — is itself covered by a
single hyperedge.  Failure of conformality is *immediately* an uncovered
clique, so the gadget of the previous section applies with no further
combinatorics: only the card `≥ 3` bound has to be checked, and it is
forced (sets of size `≤ 2` with all pairs covered are covered). -/

/-- **Conformality** (`fagin1983degrees`): every primal clique is covered
by a hyperedge. -/
def Conformal {m n : ℕ} (E : Fin m → Finset (Fin (n + 1))) : Prop :=
  ∀ C : Finset (Fin (n + 1)),
    (∀ u ∈ C, ∀ w ∈ C, u ≠ w → ∃ k, u ∈ E k ∧ w ∈ E k) → ∃ k, C ⊆ E k

/-- **Non-conformality is an uncovered clique.**  The covering hypothesis
`hcov` (every vertex lies in some hyperedge) is used only to rule out the
degenerate witnesses of size `≤ 1`; it is honest — without it a vertex in
no hyperedge is a size-1 "uncovered clique" on which the colouring gadget
has nothing to say. -/
theorem exists_uncoveredClique_of_not_conformal {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} (hcov : ∀ v, ∃ k, v ∈ E k)
    (h : ¬ Conformal E) : ∃ C, UncoveredClique E C := by
  rw [Conformal] at h
  push Not at h
  obtain ⟨C, hpairs, hunc⟩ := h
  refine ⟨C, hpairs, hunc, ?_⟩
  by_contra hcard
  push Not at hcard
  have h3 : C.card = 0 ∨ C.card = 1 ∨ C.card = 2 := by omega
  rcases h3 with hC | hC | hC
  · obtain ⟨a, ha⟩ := hcov 0
    exact hunc a (by rw [Finset.card_eq_zero.mp hC]; exact Finset.empty_subset _)
  · obtain ⟨a, hCa⟩ := Finset.card_eq_one.mp hC
    obtain ⟨k, hk⟩ := hcov a
    exact hunc k (by rw [hCa]; simpa using hk)
  · obtain ⟨a, b, hab, hCab⟩ := Finset.card_eq_two.mp hC
    obtain ⟨k, hka, hkb⟩ := hpairs a (by simp [hCab]) b (by simp [hCab]) hab
    exact hunc k (by rw [hCab]; simp [hka, hkb, Finset.insert_subset_iff])

/-- **The conformality half of the converse, unconditional.**  Any
hypergraph that is not conformal — regardless of any GYO analysis —
carries a pairwise-consistent, locally nonempty, globally unsolvable
instance over `ℕ`. -/
theorem not_conformal_pairwiseConsistent_not_solvable {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} (hcov : ∀ v, ∃ k, v ∈ E k)
    (h : ¬ Conformal E) :
    ∃ Rel : Fin m → (Fin (n + 1) → ℕ) → Prop,
      EdgeSupported E Rel ∧
      PairwiseConsistent (fun _ => (Set.univ : Set ℕ)) E Rel ∧
      (∀ k, ∃ t : Fin (n + 1) → ℕ,
        (∀ u, t u ∈ (Set.univ : Set ℕ)) ∧ Rel k t) ∧
      ¬ ∃ f : Fin (n + 1) → ℕ,
        (∀ u, f u ∈ (Set.univ : Set ℕ)) ∧ ∀ k, Rel k f := by
  obtain ⟨C, hC⟩ := exists_uncoveredClique_of_not_conformal hcov h
  exact uncoveredClique_pairwiseConsistent_not_solvable hC

/-! ### Reachable stuck states

`Ste.StuckState.exists_stuck_of_not_gyoReducible` produces a stuck state,
but `Stuck` records no relation between the live edge set `K` and the
edges outside it — `Stuck E S ∅` holds for every nonempty `S`, so the
bare predicate carries no information about `E`.  What the greedy
reduction actually maintains is stronger: **every dead edge's live trace
is dominated by a live one's** (a `contract` step deletes `k` only in
favour of a live `k'` whose live trace contains it, and shrinking `S`
preserves the inclusion).  That invariant, `dominated`, is what lets the
analysis be carried out inside the live hypergraph and then lifted back
to `E`. -/

/-- **A reachable stuck state**: stuck, plus the domination invariant of
the greedy GYO reduction. -/
structure StuckReduced {m n : ℕ} (E : Fin m → Finset (Fin (n + 1)))
    (S : Finset (Fin (n + 1))) (K : Finset (Fin m)) : Prop where
  /-- Neither GYO step applies and live vertices remain. -/
  stuck : Stuck E S K
  /-- Every dead edge's live trace is inside some live edge's live trace. -/
  dominated : ∀ k : Fin m, k ∉ K → ∃ k' ∈ K, E k ∩ S ⊆ E k' ∩ S

/-- Greedy reduction carrying the domination invariant: if no *reachable*
stuck state exists, every state satisfying the invariant reduces.  The
invariant is preserved by both GYO steps — `ear` only shrinks `S`, and
`contract` deletes `k` in favour of a live `k'`, which also re-dominates
everything `k` used to dominate. -/
theorem gyo_of_card_le_of_forall_not_stuckReduced {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} (h : ∀ S K, ¬ StuckReduced E S K) :
    ∀ (N : ℕ) (S : Finset (Fin (n + 1))) (K : Finset (Fin m)),
      S.card + K.card ≤ N →
      (∀ k : Fin m, k ∉ K → ∃ k' ∈ K, E k ∩ S ⊆ E k' ∩ S) → GYO E S K := by
  intro N
  induction N with
  | zero =>
    intro S K hle _
    have : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst this
    exact GYO.empty K
  | succ N ih =>
    intro S K hle hdom
    rcases S.eq_empty_or_nonempty with rfl | hS
    · exact GYO.empty K
    · have hnot : ¬ (NoEar E S K ∧ NoContract E S K) :=
        fun hc => h S K ⟨⟨hS, hc.1, hc.2⟩, hdom⟩
      rcases not_and_or.mp hnot with hne | hnc
      · rw [NoEar] at hne
        push Not at hne
        obtain ⟨v, hv, k₀, hk₀, hvk₀, honly⟩ := hne
        refine GYO.ear hv hk₀ hvk₀ honly (ih _ _ ?_ ?_)
        · have hcard : (S.erase v).card = S.card - 1 := Finset.card_erase_of_mem hv
          have hpos : 0 < S.card := Finset.card_pos.mpr ⟨v, hv⟩
          omega
        · intro k hk
          obtain ⟨k', hk', hsub⟩ := hdom k hk
          refine ⟨k', hk', fun u hu => ?_⟩
          rw [Finset.mem_inter, Finset.mem_erase] at hu ⊢
          have hmem := Finset.mem_inter.mp
            (hsub (Finset.mem_inter.mpr ⟨hu.1, hu.2.2⟩))
          exact ⟨hmem.1, hu.2.1, hmem.2⟩
      · rw [NoContract] at hnc
        push Not at hnc
        obtain ⟨k, hk, k', hk', hkk', hsub⟩ := hnc
        refine GYO.contract hk hk' hkk' hsub (ih _ _ ?_ ?_)
        · have hcard : (K.erase k).card = K.card - 1 := Finset.card_erase_of_mem hk
          have hpos : 0 < K.card := Finset.card_pos.mpr ⟨k, hk⟩
          omega
        · intro j hj
          rcases eq_or_ne j k with rfl | hjk
          · exact ⟨k', Finset.mem_erase.mpr ⟨hkk', hk'⟩, hsub⟩
          · have hjK : j ∉ K := fun hc =>
              hj (Finset.mem_erase.mpr ⟨hjk, hc⟩)
            obtain ⟨j', hj', hjsub⟩ := hdom j hjK
            rcases eq_or_ne j' k with rfl | hj'k
            · exact ⟨k', Finset.mem_erase.mpr ⟨hkk', hk'⟩, hjsub.trans hsub⟩
            · exact ⟨j', Finset.mem_erase.mpr ⟨hj'k, hj'⟩, hjsub⟩

/-- **A hypergraph that is not GYO-reducible has a reachable stuck
state.**  The strengthening of `exists_stuck_of_not_gyoReducible` that
the extraction needs: the initial state `(univ, univ)` satisfies the
domination invariant vacuously, and the invariant survives every step. -/
theorem exists_stuckReduced_of_not_gyoReducible {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} (h : ¬ GYOReducible E) :
    ∃ (S : Finset (Fin (n + 1))) (K : Finset (Fin m)), StuckReduced E S K := by
  by_contra hc
  push Not at hc
  exact h (gyo_of_card_le_of_forall_not_stuckReduced hc _ Finset.univ Finset.univ
    le_rfl fun k hk => absurd (Finset.mem_univ k) hk)

/-! ### What a reachable stuck state gives -/

/-- At a reachable stuck state every live vertex lies in a **live** edge:
its edge (from the covering hypothesis) is either live already or is
dominated by a live one, which then contains it too. -/
theorem exists_live_edge_of_stuckReduced {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} {S : Finset (Fin (n + 1))}
    {K : Finset (Fin m)} (hst : StuckReduced E S K)
    (hcov : ∀ v, ∃ k, v ∈ E k) {v : Fin (n + 1)} (hv : v ∈ S) :
    ∃ k ∈ K, v ∈ E k := by
  obtain ⟨k, hk⟩ := hcov v
  by_cases hkK : k ∈ K
  · exact ⟨k, hkK, hk⟩
  · obtain ⟨k', hk', hsub⟩ := hst.dominated k hkK
    exact ⟨k', hk', (Finset.mem_inter.mp (hsub (Finset.mem_inter.mpr ⟨hk, hv⟩))).1⟩

/-- **No simplicial vertex at a reachable stuck state.**  If the closed
live neighbourhood of a live vertex `v` were contained in a single live
edge `k₀`, then every live edge through `v` would have its live trace
inside `E k₀ ∩ S`, so `NoContract` would collapse it onto `k₀`; `v` would
lie in exactly one live edge and `NoEar` would fail.  This is precisely
the hypothesis that Dirac's simplicial-vertex theorem contradicts for a
chordal primal graph — see the residue note at the end of the file. -/
theorem not_simplicial_of_stuckReduced {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} {S : Finset (Fin (n + 1))}
    {K : Finset (Fin m)} (hst : StuckReduced E S K)
    {v : Fin (n + 1)} (hv : v ∈ S) {k₀ : Fin m} (hk₀ : k₀ ∈ K)
    (hvk₀ : v ∈ E k₀) :
    ¬ ∀ u ∈ S, (∃ k ∈ K, v ∈ E k ∧ u ∈ E k) → u ∈ E k₀ := by
  intro hsimp
  refine hst.stuck.2.1 v hv k₀ hk₀ hvk₀ ?_
  intro k hk hvk
  by_contra hkk₀
  refine hst.stuck.2.2 k hk k₀ hk₀ (Ne.symm hkk₀) ?_
  intro u hu
  rw [Finset.mem_inter] at hu ⊢
  exact ⟨hsimp u hu.2 ⟨k, hk, hvk, hu.1⟩, hu.2⟩

/-! ### Lifting live obstructions to the whole hypergraph

The domination invariant makes the live hypergraph faithful: a dead edge
can never see more of `S` than some live edge does.  So an obstruction
found among the live edges is an obstruction of `E`. -/

/-- A cycle that is chord-free *for the live edges* is chord-free for all
of `E`: a dead edge seeing two consecutive pairs is dominated by a live
edge, which then sees them too. -/
theorem bfmyCycle_of_live {m n p : ℕ} {E : Fin m → Finset (Fin (n + 1))}
    {S : Finset (Fin (n + 1))} {K : Finset (Fin m)} (hst : StuckReduced E S K)
    {v : Fin (p + 3) → Fin (n + 1)} (hmem : ∀ i, v i ∈ S)
    (hinj : Function.Injective v)
    (hcover : ∀ i, ∃ k ∈ K, v (i - 1) ∈ E k ∧ v i ∈ E k)
    (hchord : ∀ k ∈ K, ∀ i j : Fin (p + 3), v (i - 1) ∈ E k → v i ∈ E k →
      v (j - 1) ∈ E k → v j ∈ E k → i = j) :
    BFMYCycle E v where
  inj := hinj
  cover i := let ⟨k, _, h1, h2⟩ := hcover i; ⟨k, h1, h2⟩
  chordfree k i j h1 h2 h3 h4 := by
    by_cases hkK : k ∈ K
    · exact hchord k hkK i j h1 h2 h3 h4
    · obtain ⟨k', hk', hsub⟩ := hst.dominated k hkK
      have lift : ∀ {w : Fin (n + 1)}, w ∈ E k → w ∈ S → w ∈ E k' :=
        fun hw hwS => (Finset.mem_inter.mp (hsub (Finset.mem_inter.mpr ⟨hw, hwS⟩))).1
      exact hchord k' hk' i j (lift h1 (hmem _)) (lift h2 (hmem _))
        (lift h3 (hmem _)) (lift h4 (hmem _))

/-- A clique of live vertices uncovered by every **live** edge is
uncovered by every edge. -/
theorem uncoveredClique_of_live {m n : ℕ} {E : Fin m → Finset (Fin (n + 1))}
    {S : Finset (Fin (n + 1))} {K : Finset (Fin m)} (hst : StuckReduced E S K)
    {C : Finset (Fin (n + 1))} (hCS : C ⊆ S)
    (hpairs : ∀ u ∈ C, ∀ w ∈ C, u ≠ w → ∃ k ∈ K, u ∈ E k ∧ w ∈ E k)
    (hunc : ∀ k ∈ K, ¬ C ⊆ E k) (hcard : 3 ≤ C.card) :
    UncoveredClique E C where
  pairs u hu w hw hne := let ⟨k, _, h1, h2⟩ := hpairs u hu w hw hne; ⟨k, h1, h2⟩
  uncovered k hk := by
    by_cases hkK : k ∈ K
    · exact hunc k hkK hk
    · obtain ⟨k', hk', hsub⟩ := hst.dominated k hkK
      exact hunc k' hk' fun u hu =>
        (Finset.mem_inter.mp (hsub (Finset.mem_inter.mpr ⟨hk hu, hCS hu⟩))).1
  card := hcard

/-! ### Chordality of the primal graph

The classical form of the cycle obstruction.  Two vertices are **primal
adjacent** when some hyperedge holds both; the hypergraph is **chordal**
when every cycle of length `≥ 4` in that graph has a chord.  A chordless
cycle of length `≥ 4` is a `BFMYCycle`: a hyperedge seeing two distinct
consecutive pairs of it would make two non-consecutive cycle vertices
adjacent. -/

/-- Two vertices are adjacent in the primal graph when a hyperedge holds
both. -/
def PrimalAdj {m n : ℕ} (E : Fin m → Finset (Fin (n + 1)))
    (u w : Fin (n + 1)) : Prop := ∃ k, u ∈ E k ∧ w ∈ E k

/-- **Chordality**: every cycle of length `≥ 4` in the primal graph has a
chord — a hyperedge holding two of its non-consecutive vertices. -/
def Chordal {m n : ℕ} (E : Fin m → Finset (Fin (n + 1))) : Prop :=
  ∀ (p : ℕ) (v : Fin (p + 4) → Fin (n + 1)), Function.Injective v →
    (∀ i, PrimalAdj E (v (i - 1)) (v i)) →
    ∃ i j : Fin (p + 4), i ≠ j ∧ i ≠ j + 1 ∧ j ≠ i + 1 ∧
      PrimalAdj E (v i) (v j)

/-- On `Fin (N + 4)` a nonzero shift moves every index. -/
theorem fin_add_ne_self {N : ℕ} (i j : Fin (N + 4)) (hj : j ≠ 0) :
    i + j ≠ i := by
  intro h
  exact hj (by simpa [add_comm] using congrArg (fun x => x - i) h)

theorem fin_one_ne_zero {N : ℕ} : (1 : Fin (N + 4)) ≠ 0 := by simp

theorem fin_two_ne_zero {N : ℕ} : (1 + 1 : Fin (N + 4)) ≠ 0 := by
  simp [Fin.ext_iff, Fin.val_add, Nat.mod_eq_of_lt]

theorem fin_three_ne_zero {N : ℕ} : (1 + 1 + 1 : Fin (N + 4)) ≠ 0 := by
  simp [Fin.ext_iff, Fin.val_add, Nat.mod_eq_of_lt]

/-- **A chordless cycle of length `≥ 4` is a BFMY cycle.**  If a hyperedge
`E k` held both consecutive pairs `{v (i-1), v i}` and `{v (j-1), v j}`
with `i ≠ j`, then two *non-consecutive* cycle vertices would lie in `E k`
— a chord.  The three cases are `j = i + 1` (chord `v (i-1), v (i+1)`),
`j = i - 1` (chord `v (j-1), v i`) and `j` further away (chord
`v i, v j`); the shifts `1, 2, 3` are nonzero on `Fin (p + 4)`. -/
theorem exists_bfmyCycle_of_not_chordal {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} (h : ¬ Chordal E) :
    ∃ (p : ℕ) (v : Fin (p + 3) → Fin (n + 1)), BFMYCycle E v := by
  rw [Chordal] at h
  push Not at h
  obtain ⟨p, v, hinj, hadj, hnc⟩ := h
  refine ⟨p + 1, v, hinj, hadj, ?_⟩
  intro k i j h1 h2 h3 h4
  by_contra hij
  rcases eq_or_ne j (i + 1) with rfl | hj1
  · refine hnc (i - 1) (i + 1) ?_ ?_ ?_ ⟨k, h1, h4⟩
    · rw [← sub_ne_zero]
      have e : (i - 1) - (i + 1) = -(1 + 1) := by abel
      rw [e, neg_ne_zero]; exact fin_two_ne_zero
    · rw [← sub_ne_zero]
      have e : (i - 1) - (i + 1 + 1) = -(1 + 1 + 1) := by abel
      rw [e, neg_ne_zero]; exact fin_three_ne_zero
    · rw [← sub_ne_zero]
      have e : (i + 1) - (i - 1 + 1) = 1 := by abel
      rw [e]; exact fin_one_ne_zero
  · rcases eq_or_ne j (i - 1) with rfl | hj2
    · refine hnc (i - 1 - 1) i ?_ ?_ ?_ ⟨k, h3, h2⟩
      · rw [← sub_ne_zero]
        have e : (i - 1 - 1) - i = -(1 + 1) := by abel
        rw [e, neg_ne_zero]; exact fin_two_ne_zero
      · rw [← sub_ne_zero]
        have e : (i - 1 - 1) - (i + 1) = -(1 + 1 + 1) := by abel
        rw [e, neg_ne_zero]; exact fin_three_ne_zero
      · rw [← sub_ne_zero]
        have e : i - (i - 1 - 1 + 1) = 1 := by abel
        rw [e]; exact fin_one_ne_zero
    · refine hnc i j hij ?_ hj1 ⟨k, h2, h4⟩
      intro hc
      exact hj2 (by rw [hc]; simp)

/-! ### The converse witness from either obstruction -/

/-- **Either obstruction yields the counterexample instance.**  An
uncovered clique feeds the colouring gadget, a BFMY cycle the parity
gadget; both produce edge-supported, pairwise-consistent, locally
nonempty relations over `ℕ` with no global solution. -/
theorem obstruction_pairwiseConsistent_not_solvable {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))}
    (h : (∃ C, UncoveredClique E C) ∨
      ∃ (p : ℕ) (v : Fin (p + 3) → Fin (n + 1)), BFMYCycle E v) :
    ∃ Rel : Fin m → (Fin (n + 1) → ℕ) → Prop,
      EdgeSupported E Rel ∧
      PairwiseConsistent (fun _ => (Set.univ : Set ℕ)) E Rel ∧
      (∀ k, ∃ t : Fin (n + 1) → ℕ,
        (∀ u, t u ∈ (Set.univ : Set ℕ)) ∧ Rel k t) ∧
      ¬ ∃ f : Fin (n + 1) → ℕ,
        (∀ u, f u ∈ (Set.univ : Set ℕ)) ∧ ∀ k, Rel k f := by
  rcases h with ⟨C, hC⟩ | ⟨p, v, hv⟩
  · exact uncoveredClique_pairwiseConsistent_not_solvable hC
  · exact bfmyCycle_pairwiseConsistent_not_solvable hv

/-- **The converse BFMY direction from the classical obstructions.**  A
hypergraph that is not conformal, or whose primal graph is not chordal,
carries a pairwise-consistent, locally nonempty, globally unsolvable
instance over `ℕ`.  Since α-acyclicity *is* conformality plus chordality
(`fagin1983degrees`), this is the converse direction modulo the
extraction recorded in the residue note below. -/
theorem not_conformal_or_not_chordal_pairwiseConsistent_not_solvable {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} (hcov : ∀ v, ∃ k, v ∈ E k)
    (h : ¬ Conformal E ∨ ¬ Chordal E) :
    ∃ Rel : Fin m → (Fin (n + 1) → ℕ) → Prop,
      EdgeSupported E Rel ∧
      PairwiseConsistent (fun _ => (Set.univ : Set ℕ)) E Rel ∧
      (∀ k, ∃ t : Fin (n + 1) → ℕ,
        (∀ u, t u ∈ (Set.univ : Set ℕ)) ∧ Rel k t) ∧
      ¬ ∃ f : Fin (n + 1) → ℕ,
        (∀ u, f u ∈ (Set.univ : Set ℕ)) ∧ ∀ k, Rel k f := by
  refine obstruction_pairwiseConsistent_not_solvable ?_
  rcases h with hnc | hnch
  · exact Or.inl (exists_uncoveredClique_of_not_conformal hcov hnc)
  · exact Or.inr (exists_bfmyCycle_of_not_chordal hnch)

/-- **The BFMY equivalence, conditional on the extraction step.**  Under
the extraction hypothesis `hext` — "not GYO-reducible implies not
conformal or not chordal", the classical structure theorem whose only
missing ingredient is Dirac's simplicial-vertex theorem (see the residue
note) — GYO-reducibility is *equivalent* to the statement that every
pairwise-consistent, locally nonempty, edge-supported instance over `ℕ`
has a global solution.  The forward implication is
`gyoReducible_pairwiseConsistent_solvable` of `Ste.AcyclicSolvability`;
the backward one is this file's gadgets.  Note the quantifier form: the
right-hand side ranges over *all* relation families on the single
concrete alphabet `ℕ` with full domains, which is exactly what the two
gadgets produce, so no alphabet quantifier is needed. -/
theorem gyoReducible_iff_pairwiseConsistent_solvable {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} (hcov : ∀ v, ∃ k, v ∈ E k)
    (hext : ¬ GYOReducible E → (¬ Conformal E ∨ ¬ Chordal E)) :
    GYOReducible E ↔
      ∀ Rel : Fin m → (Fin (n + 1) → ℕ) → Prop, EdgeSupported E Rel →
        PairwiseConsistent (fun _ => (Set.univ : Set ℕ)) E Rel →
        (∀ k, ∃ t : Fin (n + 1) → ℕ,
          (∀ u, t u ∈ (Set.univ : Set ℕ)) ∧ Rel k t) →
        ∃ f : Fin (n + 1) → ℕ,
          (∀ u, f u ∈ (Set.univ : Set ℕ)) ∧ ∀ k, Rel k f := by
  constructor
  · intro hgyo Rel hsupp hpc hloc
    exact gyoReducible_pairwiseConsistent_solvable hgyo hsupp hpc hloc
      fun _ => ⟨0, trivial⟩
  · intro hall
    by_contra hgyo
    obtain ⟨Rel, hsupp, hpc, hloc, hns⟩ :=
      not_conformal_or_not_chordal_pairwiseConsistent_not_solvable hcov (hext hgyo)
    exact hns (hall Rel hsupp hpc hloc)

/-- **Every live vertex has two non-adjacent neighbours.**  At a
reachable stuck state of a *conformal* hypergraph, no vertex of `S` is
simplicial in the primal graph: if the closed neighbourhood `N` of `v`
inside `S` were a clique, conformality would put `N` inside a hyperedge,
domination would move that hyperedge into `K`, and
`not_simplicial_of_stuckReduced` would be contradicted.

Together with the observation that on `S` primal adjacency and *live*
adjacency coincide (a dead edge holding two live vertices is dominated by
a live one), this is exactly the hypothesis of Dirac's simplicial-vertex
theorem — see the residue note at the end of the file. -/
theorem exists_nonadjacent_neighbours_of_stuckReduced {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} {S : Finset (Fin (n + 1))}
    {K : Finset (Fin m)} (hst : StuckReduced E S K)
    (hcov : ∀ v, ∃ k, v ∈ E k) (hconf : Conformal E)
    {v : Fin (n + 1)} (hv : v ∈ S) :
    ∃ u ∈ S, ∃ w ∈ S, PrimalAdj E v u ∧ PrimalAdj E v w ∧ ¬ PrimalAdj E u w := by
  classical
  obtain ⟨k₀, hk₀, hvk₀⟩ := exists_live_edge_of_stuckReduced hst hcov hv
  set N : Finset (Fin (n + 1)) := S.filter (fun u => PrimalAdj E v u) with hN
  have hmemN : ∀ u, u ∈ N ↔ (u ∈ S ∧ PrimalAdj E v u) := by
    intro u; rw [hN, Finset.mem_filter]
  have hvN : v ∈ N := (hmemN v).mpr ⟨hv, ⟨k₀, hvk₀, hvk₀⟩⟩
  by_contra hcon
  push Not at hcon
  -- `N` is a clique
  have hclique : ∀ u ∈ N, ∀ w ∈ N, u ≠ w → ∃ k, u ∈ E k ∧ w ∈ E k := by
    intro u hu w hw _
    obtain ⟨huS, huA⟩ := (hmemN u).mp hu
    obtain ⟨hwS, hwA⟩ := (hmemN w).mp hw
    exact hcon u huS w hwS huA hwA
  obtain ⟨k, hk⟩ := hconf N hclique
  -- move the covering hyperedge into `K`
  obtain ⟨k', hk', hcov'⟩ : ∃ k' ∈ K, N ⊆ E k' := by
    by_cases hkK : k ∈ K
    · exact ⟨k, hkK, hk⟩
    · obtain ⟨k', hk'K, hsub⟩ := hst.dominated k hkK
      refine ⟨k', hk'K, fun u hu => ?_⟩
      exact (Finset.mem_inter.mp
        (hsub (Finset.mem_inter.mpr ⟨hk hu, ((hmemN u).mp hu).1⟩))).1
  refine not_simplicial_of_stuckReduced hst hv hk' (hcov' hvN) ?_
  intro u huS hu
  obtain ⟨j, _, hvj, huj⟩ := hu
  exact hcov' ((hmemN u).mpr ⟨huS, ⟨j, hvj, huj⟩⟩)

/-- On the live vertex set, primal adjacency is *live* adjacency: a dead
hyperedge holding two live vertices is dominated by a live one. -/
theorem primalAdj_live_of_stuckReduced {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} {S : Finset (Fin (n + 1))}
    {K : Finset (Fin m)} (hst : StuckReduced E S K)
    {u w : Fin (n + 1)} (hu : u ∈ S) (hw : w ∈ S) (h : PrimalAdj E u w) :
    ∃ k ∈ K, u ∈ E k ∧ w ∈ E k := by
  obtain ⟨k, h1, h2⟩ := h
  by_cases hkK : k ∈ K
  · exact ⟨k, hkK, h1, h2⟩
  · obtain ⟨k', hk', hsub⟩ := hst.dominated k hkK
    exact ⟨k', hk',
      (Finset.mem_inter.mp (hsub (Finset.mem_inter.mpr ⟨h1, hu⟩))).1,
      (Finset.mem_inter.mp (hsub (Finset.mem_inter.mpr ⟨h2, hw⟩))).1⟩

/-! ### The residue: Dirac's simplicial-vertex theorem

Everything above is `sorry`-free.  What is *not* mechanized here is one
purely graph-theoretic classical fact, isolated below as
`DiracHypothesis`: a finite graph in which no vertex is simplicial
contains a chordless cycle of length `≥ 4` (Dirac 1961; equivalently,
every chordal graph has a simplicial vertex).  Given it, the extraction
closes — `extraction_of_dirac` — and with it the full converse
(`not_gyoReducible_exists_pairwiseConsistent_not_solvable`) and the
biconditional against `gyoReducible_pairwiseConsistent_solvable`.

The reason it is isolated rather than proved: the standard argument goes
through minimal `a`–`b` separators, needs connected components and
shortest paths inside them, and rebuilds a chordless cycle by
concatenating two such paths — a development orthogonal to everything in
this file. -/

/-- **Dirac's simplicial-vertex theorem**, in the exact induced-subgraph
form the extraction consumes: if no vertex of `S` is simplicial in the
primal graph — every `v ∈ S` has two `S`-neighbours that are not adjacent
— then `S` carries a chordless cycle of length `≥ 4`. -/
def DiracHypothesis {m n : ℕ} (E : Fin m → Finset (Fin (n + 1))) : Prop :=
  ∀ S : Finset (Fin (n + 1)), S.Nonempty →
    (∀ v ∈ S, ∃ u ∈ S, ∃ w ∈ S,
      PrimalAdj E v u ∧ PrimalAdj E v w ∧ ¬ PrimalAdj E u w) →
    ∃ (p : ℕ) (c : Fin (p + 4) → Fin (n + 1)),
      (∀ i, c i ∈ S) ∧ Function.Injective c ∧
      (∀ i, PrimalAdj E (c (i - 1)) (c i)) ∧
      ∀ i j : Fin (p + 4), i ≠ j → i ≠ j + 1 → j ≠ i + 1 →
        ¬ PrimalAdj E (c i) (c j)

/-- **Non-α-acyclic and conformal implies non-chordal**, given Dirac.  The
reachable stuck state supplies a nonempty `S` with no simplicial vertex
(`exists_nonadjacent_neighbours_of_stuckReduced`); Dirac turns that into
a chordless cycle of length `≥ 4`, which is precisely a failure of
`Chordal`. -/
theorem not_chordal_of_not_gyoReducible {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} (hcov : ∀ v, ∃ k, v ∈ E k)
    (hdirac : DiracHypothesis E) (hconf : Conformal E)
    (h : ¬ GYOReducible E) : ¬ Chordal E := by
  obtain ⟨S, K, hst⟩ := exists_stuckReduced_of_not_gyoReducible h
  obtain ⟨p, c, -, hinj, hadj, hchord⟩ := hdirac S hst.stuck.1
    fun v hv => exists_nonadjacent_neighbours_of_stuckReduced hst hcov hconf hv
  intro hch
  obtain ⟨i, j, h1, h2, h3, h4⟩ := hch p c hinj hadj
  exact hchord i j h1 h2 h3 h4

/-- **The extraction, given Dirac**: a hypergraph that is not
GYO-reducible is not conformal or not chordal. -/
theorem extraction_of_dirac {m n : ℕ} {E : Fin m → Finset (Fin (n + 1))}
    (hcov : ∀ v, ∃ k, v ∈ E k) (hdirac : DiracHypothesis E)
    (h : ¬ GYOReducible E) : ¬ Conformal E ∨ ¬ Chordal E := by
  by_cases hconf : Conformal E
  · exact Or.inr (not_chordal_of_not_gyoReducible hcov hdirac hconf h)
  · exact Or.inl hconf

/-- **The full converse BFMY direction, given Dirac.**  Every hypergraph
that is not GYO-reducible (with every vertex covered) carries relations
over `ℕ` that are edge-supported, pairwise consistent, locally nonempty
and globally unsolvable. -/
theorem not_gyoReducible_exists_pairwiseConsistent_not_solvable {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} (hcov : ∀ v, ∃ k, v ∈ E k)
    (hdirac : DiracHypothesis E) (h : ¬ GYOReducible E) :
    ∃ Rel : Fin m → (Fin (n + 1) → ℕ) → Prop,
      EdgeSupported E Rel ∧
      PairwiseConsistent (fun _ => (Set.univ : Set ℕ)) E Rel ∧
      (∀ k, ∃ t : Fin (n + 1) → ℕ,
        (∀ u, t u ∈ (Set.univ : Set ℕ)) ∧ Rel k t) ∧
      ¬ ∃ f : Fin (n + 1) → ℕ,
        (∀ u, f u ∈ (Set.univ : Set ℕ)) ∧ ∀ k, Rel k f :=
  not_conformal_or_not_chordal_pairwiseConsistent_not_solvable hcov
    (extraction_of_dirac hcov hdirac h)

/-- **The BFMY equivalence, given Dirac.**  GYO-reducibility is
equivalent to "pairwise consistency implies global consistency" for
edge-supported instances over `ℕ` with full domains: forward by
`gyoReducible_pairwiseConsistent_solvable`, backward by this file's two
gadgets. -/
theorem gyoReducible_iff_pairwiseConsistent_solvable_of_dirac {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} (hcov : ∀ v, ∃ k, v ∈ E k)
    (hdirac : DiracHypothesis E) :
    GYOReducible E ↔
      ∀ Rel : Fin m → (Fin (n + 1) → ℕ) → Prop, EdgeSupported E Rel →
        PairwiseConsistent (fun _ => (Set.univ : Set ℕ)) E Rel →
        (∀ k, ∃ t : Fin (n + 1) → ℕ,
          (∀ u, t u ∈ (Set.univ : Set ℕ)) ∧ Rel k t) →
        ∃ f : Fin (n + 1) → ℕ,
          (∀ u, f u ∈ (Set.univ : Set ℕ)) ∧ ∀ k, Rel k f :=
  gyoReducible_iff_pairwiseConsistent_solvable hcov (extraction_of_dirac hcov hdirac)

/-! ### Sanity checks on the canonical example -/

/-- The triangle `cycleE 0` (`= triangleE` of `Ste.AcyclicConverse`) has
an uncovered clique: all three vertices are pairwise covered, and no edge
holds all three. -/
example : UncoveredClique (cycleE 0) {0, 1, 2} := ⟨by decide, by decide, by decide⟩

/-- Hence the triangle is not conformal, and this file's colouring gadget
reproduces — over `ℕ` instead of `Bool` — the converse witness that
`Ste.AcyclicConverse.triangle_pairwiseConsistent_not_solvable` gives via
the parity gadget. -/
example : ¬ Conformal (cycleE 0) := fun hconf =>
  (⟨by decide, by decide, by decide⟩ :
    UncoveredClique (cycleE 0) {0, 1, 2}).uncovered
      (hconf {0, 1, 2} (by decide)).choose (hconf {0, 1, 2} (by decide)).choose_spec

end STE
