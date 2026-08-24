/-
The converse BFMY direction: necessity of acyclicity — witnessed on the
canonical cyclic family.

`Ste.AcyclicSolvability` mechanizes the *solvability* half of the
Beeri–Fagin–Maier–Yannakakis equivalence
(`gyoReducible_pairwiseConsistent_solvable`): on a GYO-reducible
(α-acyclic) hypergraph, pairwise-consistent nonempty edge relations
always admit a global solution.  Its honest-residue note (4) records
that the *converse* — that acyclicity is **necessary** for pairwise
consistency to guarantee global consistency — was not claimed.  This
file discharges that item for the canonical infinite family of
non-acyclic hypergraphs, the cycles.

**What is mechanized.**

1. **The concrete base case — the triangle** (`triangleE`, the
   hypergraph `![{0,1}, {1,2}, {0,2}]` on `Fin 3`):
   * `triangle_not_gyoReducible` — the triangle is not GYO-reducible:
     every vertex lies in exactly two edges (no ear), and no edge's
     restriction to the live vertices is contained in another's (no
     contraction), so no first reduction step exists at the full state.
   * `triangle_pairwiseConsistent_not_solvable` — the frustrated XOR
     instance over `Bool`: each edge `{k, k+1}` carries the parity
     relation `g k ⊕ g (k+1) = a k` with odd total parity.  It is
     `EdgeSupported`, `PairwiseConsistent` (every relation projects
     onto *both* Boolean values at each of its vertices, so any tuple
     of one edge matches some tuple of any other on their at-most-one
     shared vertex), every table is nonempty — yet no global solution
     exists: XOR-ing the constraints around the cycle telescopes to
     `false`, contradicting the odd parity.
2. **The general cycle** (`cycleE n`, edges `{k, k+1}` mod `n + 3` for
   every `n`, i.e. every cycle length `≥ 3`):
   `cycle_not_gyoReducible` and `cycle_pairwiseConsistent_not_solvable`
   upgrade the converse witness from one instance to the infinite
   family.  The frustrated parameter is `oddParam` (exactly one odd
   edge); pairwise consistency holds for *every* parameter
   (`cycleRel_pairwiseConsistent`), unsolvability for the odd one
   (`cycleOdd_not_solvable`).  The triangle results are the `n = 0`
   instance (`triangleE_eq_cycleE`).
3. **NOT mechanized — the honest residue**: the full converse, that
   *every* non-GYO-reducible hypergraph (with every vertex in some
   edge) supports a pairwise-consistent unsolvable instance.  The
   classical proof (BFMY 1983, Thm. 3.4 direction (2)⇒(1) via Fagin's
   degrees of acyclicity) extracts a weak β-cycle from non-acyclicity
   and plants exactly the parity gadget of this file on it; extracting
   that cycle from `¬ GYOReducible` is a substantial combinatorial
   development (chordality/conformality of the primal graph) that is
   left open here.  What items (1)–(2) establish is that the converse
   holds on the canonical family: for every cycle length the
   implication "pairwise consistent ⇒ globally consistent" *fails*,
   so the acyclicity hypothesis of
   `gyoReducible_pairwiseConsistent_solvable` cannot be dropped.

**Relation to `Ste.TwistedNonvanishing`.**  The witness is the same
gadget as that file's frustrated XOR triangle (`xorTriangle`,
`Frustrated`), generalized from 3 to any cycle length: there the odd
parity survives linearization as a nonzero relative Čech `Ȟ¹` class
(the cohomological reading of local-consistent-but-globally-
inconsistent); here the very same frustration is read as a
database-theoretic counterexample — pairwise consistency (full
semijoin reduction changes nothing: every semijoin is already full)
without global consistency.  One obstruction, two readings.

There is no `sorry` in this file: every statement made is proved.

References: C. Beeri, R. Fagin, D. Maier, M. Yannakakis, *On the
desirability of acyclic database schemes*, JACM 30(3):479–513, 1983
(`beeri1983acyclic`) — the equivalence theorem's hard direction:
pairwise consistency implies total consistency *only if* the scheme is
α-acyclic, proved by planting a parity counterexample on a cycle of
the non-acyclic scheme; R. Fagin, *Degrees of acyclicity for
hypergraphs and relational database schemes*, JACM 30(3):514–550, 1983
(`fagin1983degrees`) — α/β/γ-acyclicity and the weak-β-cycle
extraction.
-/
import Mathlib.Data.Fin.VecNotation
import Ste.AcyclicSolvability

namespace STE

open Set

/-! ### Fin arithmetic on the cycle `Fin (n + 3)`

Small toolkit: on a cycle of length at least 3, one step and two steps
never return to the start, and one step is injective.  Everything is
proved from the core `Fin.val_add_one` case split. -/

/-- On `Fin (n + 3)`, `v + 1 ≠ v`. -/
theorem cycle_add_one_ne {n : ℕ} (v : Fin (n + 2 + 1)) : v + 1 ≠ v := by
  intro h
  have hv : ((v + 1 : Fin (n + 2 + 1))).val = v.val := congrArg Fin.val h
  rw [Fin.val_add_one] at hv
  by_cases hl : v = Fin.last (n + 2)
  · rw [if_pos hl] at hv
    have hval : v.val = n + 2 := by rw [hl]; rfl
    omega
  · rw [if_neg hl] at hv
    omega

/-- On `Fin (n + 3)`, `v + 1 + 1 ≠ v` — two steps along a cycle of
length at least 3 do not close it. -/
theorem cycle_add_two_ne {n : ℕ} (v : Fin (n + 2 + 1)) : v + 1 + 1 ≠ v := by
  intro h
  have hc : ((v + 1 + 1 : Fin (n + 2 + 1))).val = v.val := congrArg Fin.val h
  have h1 := Fin.val_add_one (v + 1)
  have h2 := Fin.val_add_one v
  by_cases hv : v = Fin.last (n + 2)
  · rw [if_pos hv] at h2
    by_cases hv1 : v + 1 = Fin.last (n + 2)
    · have hb : ((v + 1 : Fin (n + 2 + 1))).val = n + 2 := by rw [hv1]; rfl
      omega
    · rw [if_neg hv1] at h1
      have ha : v.val = n + 2 := by rw [hv]; rfl
      omega
  · rw [if_neg hv] at h2
    by_cases hv1 : v + 1 = Fin.last (n + 2)
    · rw [if_pos hv1] at h1
      have hb : ((v + 1 : Fin (n + 2 + 1))).val = n + 2 := by rw [hv1]; rfl
      omega
    · rw [if_neg hv1] at h1
      omega

/-! ### The cycle hypergraph and its non-reducibility -/

/-- **The cycle hypergraph** on `n + 3 ≥ 3` vertices: edge `k` is the
pair `{k, k + 1}` (indices mod `n + 3`).  For `n = 0` this is the
triangle (`triangleE_eq_cycleE`), the primal-graph shape of
`Ste.TwistedNonvanishing.triangleCover`. -/
def cycleE (n : ℕ) : Fin (n + 2 + 1) → Finset (Fin (n + 2 + 1)) :=
  fun k => {k, k + 1}

theorem mem_cycleE {n : ℕ} {k v : Fin (n + 2 + 1)} :
    v ∈ cycleE n k ↔ v = k ∨ v = k + 1 := by
  simp [cycleE]

/-- **A first GYO step exists at any nonempty state**: inversion of the
`GYO` derivation.  Either some live vertex is an ear, or some live edge
is contracted into another. -/
theorem gyo_first_step {m n : ℕ} {E : Fin m → Finset (Fin (n + 1))}
    {S : Finset (Fin (n + 1))} {K : Finset (Fin m)}
    (h : GYO E S K) (hS : S.Nonempty) :
    (∃ v ∈ S, ∃ k₀ ∈ K, v ∈ E k₀ ∧ ∀ k ∈ K, v ∈ E k → k = k₀) ∨
    (∃ k ∈ K, ∃ k' ∈ K, k' ≠ k ∧ E k ∩ S ⊆ E k' ∩ S) := by
  cases h with
  | empty K => exact absurd hS Finset.not_nonempty_empty
  | ear hv hk₀ hvk₀ honly h => exact Or.inl ⟨_, hv, _, hk₀, hvk₀, honly⟩
  | contract hk hk' hne hsub h => exact Or.inr ⟨_, hk, _, hk', hne, hsub⟩

/-- **The cycle is not GYO-reducible** — no first step exists at the
full state: every vertex `v` lies in the two distinct live edges
`v - 1` and `v` (no ear), and no edge `{k, k+1}` is contained in
another `{k', k'+1}` on a cycle of length ≥ 3 (no contraction). -/
theorem cycle_not_gyoReducible (n : ℕ) : ¬ GYOReducible (cycleE n) := by
  intro h
  rcases gyo_first_step h ⟨0, Finset.mem_univ 0⟩ with
    ⟨v, -, k₀, -, -, honly⟩ | ⟨k, -, k', -, hne, hsub⟩
  · -- ear: `v` would lie in only one live edge, but it lies in
    -- edges `v` and `v - 1`, which are distinct.
    have h1 : v = k₀ :=
      honly v (Finset.mem_univ v) (mem_cycleE.mpr (Or.inl rfl))
    have hsub1 : v - 1 + 1 = v := by simp
    have h2 : v - 1 = k₀ :=
      honly (v - 1) (Finset.mem_univ _)
        (mem_cycleE.mpr (Or.inr hsub1.symm))
    have h3 : v - 1 = v := h2.trans h1.symm
    have h4 : v = v + 1 := by
      conv_lhs => rw [← hsub1, h3]
    exact cycle_add_one_ne v h4.symm
  · -- contraction: `{k, k+1} ⊆ {k', k'+1}` with `k ≠ k'` forces the
    -- cycle to have length 2.
    rw [Finset.inter_univ, Finset.inter_univ] at hsub
    have h1 : k ∈ cycleE n k' := hsub (mem_cycleE.mpr (Or.inl rfl))
    have h2 : k + 1 ∈ cycleE n k' := hsub (mem_cycleE.mpr (Or.inr rfl))
    rcases mem_cycleE.mp h1 with h1' | h1'
    · exact hne h1'.symm
    · rcases mem_cycleE.mp h2 with h2' | h2'
      · -- k = k' + 1 and k + 1 = k' give k = k + 1 + 1
        have : k + 1 + 1 = k := by rw [h2', ← h1']
        exact cycle_add_two_ne k this
      · exact hne (add_right_cancel h2').symm

/-! ### The frustrated XOR chain on the cycle -/

/-- **The XOR edge relation** with twist parameter `a`: edge `k`
requires `g k ⊕ g (k + 1) = a k`.  This is the cyclic generalization of
`Ste.TwistedNonvanishing.xorTriangle`'s pair constraints. -/
def cycleRel (n : ℕ) (a : Fin (n + 2 + 1) → Bool) :
    Fin (n + 2 + 1) → (Fin (n + 2 + 1) → Bool) → Prop :=
  fun k g => Bool.xor (g k) (g (k + 1)) = a k

/-- **The odd (frustrated) parameter**: exactly one edge — edge `0` —
is twisted.  Total parity odd, so the cycle is frustrated. -/
def oddParam (n : ℕ) : Fin (n + 2 + 1) → Bool :=
  fun k => decide (k = 0)

/-- The XOR relations have edge scope. -/
theorem cycleRel_edgeSupported (n : ℕ) (a : Fin (n + 2 + 1) → Bool) :
    EdgeSupported (cycleE n) (cycleRel n a) := by
  intro k g g' hag
  unfold cycleRel
  rw [hag k (mem_cycleE.mpr (Or.inl rfl)),
    hag (k + 1) (mem_cycleE.mpr (Or.inr rfl))]

/-- **Every table is nonempty** — for any twist: pick `false` at the
low vertex and the forced value at the high vertex. -/
theorem cycleRel_tables_nonempty (n : ℕ) (a : Fin (n + 2 + 1) → Bool)
    (k : Fin (n + 2 + 1)) :
    ∃ t : Fin (n + 2 + 1) → Bool,
      (∀ u, t u ∈ (Set.univ : Set Bool)) ∧ cycleRel n a k t := by
  refine ⟨fun v => if v = k then false else a k, fun _ => trivial, ?_⟩
  unfold cycleRel
  simp [cycle_add_one_ne k]

/-- **Pairwise consistency — for every twist parameter, frustrated or
not.**  Each XOR relation projects onto *both* Boolean values at each
of its two vertices, and two distinct edges of a cycle of length ≥ 3
share at most one vertex; so any tuple of one edge can be matched by a
tuple of any other edge agreeing on the shared vertex, by propagating
the shared value through the second edge's parity constraint.  A full
semijoin pass leaves the frustrated instance untouched: it is already
semijoin-reduced. -/
theorem cycleRel_pairwiseConsistent (n : ℕ) (a : Fin (n + 2 + 1) → Bool) :
    PairwiseConsistent (fun _ => (Set.univ : Set Bool)) (cycleE n)
      (cycleRel n a) := by
  intro k k' g hgD hgk
  by_cases hkk : k' = k
  · exact ⟨g, hgD, hkk ▸ hgk, fun _ _ => rfl⟩
  by_cases hadj : k = k' + 1
  · -- shared vertex is `k = k' + 1`, the high vertex of edge `k'`:
    -- fix `g` there, back-propagate to `k'`.
    subst hadj
    refine ⟨Function.update g k' (Bool.xor (g (k' + 1)) (a k')),
      fun _ => trivial, ?_, ?_⟩
    · unfold cycleRel
      rw [Function.update_self,
        Function.update_of_ne (cycle_add_one_ne k')]
      cases g (k' + 1) <;> cases a k' <;> rfl
    · intro u hu
      rcases eq_or_ne u k' with heq | hun
      · exfalso
        have huk : u ∈ cycleE n (k' + 1) := (Finset.mem_inter.mp hu).1
        rw [heq] at huk
        rcases mem_cycleE.mp huk with h | h
        · exact cycle_add_one_ne k' h.symm
        · exact cycle_add_two_ne k' h.symm
      · rw [Function.update_of_ne hun]
  · -- shared vertex (if any) is `k'`, the low vertex of edge `k'`:
    -- fix `g` there, forward-propagate to `k' + 1`.
    refine ⟨Function.update g (k' + 1) (Bool.xor (g k') (a k')),
      fun _ => trivial, ?_, ?_⟩
    · unfold cycleRel
      rw [Function.update_self,
        Function.update_of_ne (Ne.symm (cycle_add_one_ne k'))]
      cases g k' <;> cases a k' <;> rfl
    · intro u hu
      rcases eq_or_ne u (k' + 1) with heq | hun
      · exfalso
        have huk : u ∈ cycleE n k := (Finset.mem_inter.mp hu).1
        rcases mem_cycleE.mp huk with h | h
        · rw [h] at heq
          exact hadj heq
        · rw [h] at heq
          exact hkk (add_right_cancel heq.symm)
      · rw [Function.update_of_ne hun]

/-- Each constraint forces the next value around the cycle. -/
theorem cycleRel_step {n : ℕ} {a : Fin (n + 2 + 1) → Bool}
    {f : Fin (n + 2 + 1) → Bool} (hf : ∀ k, cycleRel n a k f)
    (k : Fin (n + 2 + 1)) : f (k + 1) = Bool.xor (f k) (a k) := by
  have h := hf k
  unfold cycleRel at h
  rw [← h]
  cases hb : f k <;> cases hb' : f (k + 1) <;> rfl

/-- **The frustrated cycle has no global solution**: the constraints
force `f` to be constant except for one flip at edge `0`, so going once
around the cycle returns `¬ f 0` at `f 0`. -/
theorem cycleOdd_not_solvable (n : ℕ) :
    ¬ ∃ f : Fin (n + 2 + 1) → Bool,
      (∀ u, f u ∈ (Set.univ : Set Bool)) ∧
      ∀ k, cycleRel n (oddParam n) k f := by
  rintro ⟨f, -, hf⟩
  -- every vertex after 0 carries the flipped value
  have hval : ∀ j : ℕ, ∀ hj : j < n + 2 + 1, 1 ≤ j →
      f ⟨j, hj⟩ = ! (f 0) := by
    intro j
    induction j with
    | zero => intro _ h; omega
    | succ i ih =>
        intro hj hi1
        by_cases hi0 : i = 0
        · subst hi0
          have h0 := cycleRel_step hf 0
          have hop : oddParam n (0 : Fin (n + 2 + 1)) = true := by
            simp [oddParam]
          rw [hop, Bool.xor_true] at h0
          have hnl : (0 : Fin (n + 2 + 1)) ≠ Fin.last (n + 2) := by
            intro hcon
            have := congrArg Fin.val hcon
            simp [Fin.val_last] at this
          have he : (0 : Fin (n + 2 + 1)) + 1 = ⟨1, hj⟩ := by
            apply Fin.ext
            rw [Fin.val_add_one, if_neg hnl]
            rfl
          rw [← he, h0]
        · have hi' : i < n + 2 + 1 := by omega
          have hprev := ih hi' (by omega)
          have hne0 : (⟨i, hi'⟩ : Fin (n + 2 + 1)) ≠ 0 := by
            intro hcon
            have := congrArg Fin.val hcon
            simp at this
            omega
          have hop : oddParam n (⟨i, hi'⟩ : Fin (n + 2 + 1)) = false := by
            simp [oddParam, hne0]
          have hstep := cycleRel_step hf ⟨i, hi'⟩
          rw [hop, Bool.xor_false, hprev] at hstep
          have hnl : (⟨i, hi'⟩ : Fin (n + 2 + 1)) ≠ Fin.last (n + 2) := by
            intro hcon
            have := congrArg Fin.val hcon
            simp [Fin.val_last] at this
            omega
          have he : (⟨i, hi'⟩ : Fin (n + 2 + 1)) + 1 = ⟨i + 1, hj⟩ := by
            apply Fin.ext
            rw [Fin.val_add_one, if_neg hnl]
          rw [← he, hstep]
  -- close the cycle at the last vertex
  have hlt : n + 2 < n + 2 + 1 := by omega
  have hlast := hval (n + 2) hlt (by omega)
  have hlaste : (⟨n + 2, hlt⟩ : Fin (n + 2 + 1)) = Fin.last (n + 2) := rfl
  have hwrap : (⟨n + 2, hlt⟩ : Fin (n + 2 + 1)) + 1 = 0 := by
    rw [hlaste]; exact Fin.last_add_one _
  have hne0 : (⟨n + 2, hlt⟩ : Fin (n + 2 + 1)) ≠ 0 := by
    intro hcon
    have := congrArg Fin.val hcon
    simp at this
  have hop : oddParam n (⟨n + 2, hlt⟩ : Fin (n + 2 + 1)) = false := by
    simp [oddParam, hne0]
  have hstep := cycleRel_step hf ⟨n + 2, hlt⟩
  rw [hwrap, hop, Bool.xor_false, hlast] at hstep
  -- hstep : f 0 = ! f 0
  cases hb : f 0 <;> rw [hb] at hstep <;> exact Bool.noConfusion hstep

/-! ### The converse witness, general cycle -/

/-- **The converse BFMY direction on the infinite cyclic family**: for
every cycle length `≥ 3`, the cycle hypergraph is *not* GYO-reducible,
and it carries edge relations — the frustrated XOR chain — that are
edge-supported, pairwise consistent (already semijoin-reduced), with
every table nonempty, yet with **no** global solution.  So pairwise
consistency does not imply global consistency beyond acyclicity: the
GYO hypothesis of `gyoReducible_pairwiseConsistent_solvable` cannot be
dropped, for any member of this family. -/
theorem cycle_pairwiseConsistent_not_solvable (n : ℕ) :
    ¬ GYOReducible (cycleE n) ∧
    ∃ Rel : Fin (n + 2 + 1) → (Fin (n + 2 + 1) → Bool) → Prop,
      EdgeSupported (cycleE n) Rel ∧
      PairwiseConsistent (fun _ => (Set.univ : Set Bool)) (cycleE n) Rel ∧
      (∀ k, ∃ t : Fin (n + 2 + 1) → Bool,
        (∀ u, t u ∈ (Set.univ : Set Bool)) ∧ Rel k t) ∧
      ¬ ∃ f : Fin (n + 2 + 1) → Bool,
        (∀ u, f u ∈ (Set.univ : Set Bool)) ∧ ∀ k, Rel k f :=
  ⟨cycle_not_gyoReducible n,
    cycleRel n (oddParam n),
    cycleRel_edgeSupported n (oddParam n),
    cycleRel_pairwiseConsistent n (oddParam n),
    cycleRel_tables_nonempty n (oddParam n),
    cycleOdd_not_solvable n⟩

/-! ### The concrete base case: the triangle -/

/-- **The triangle hypergraph** `![{0,1}, {1,2}, {0,2}]` on `Fin 3` —
the smallest non-acyclic hypergraph, and the scope structure of
`Ste.TwistedNonvanishing.triangleCover`. -/
def triangleE : Fin 3 → Finset (Fin 3) :=
  ![{0, 1}, {1, 2}, {0, 2}]

/-- The triangle is the 3-cycle: same edges (edge `2` is `{0, 2} =
{2, 2 + 1}` as a `Finset`). -/
theorem triangleE_eq_cycleE : triangleE = cycleE 0 := by
  decide

/-- **The triangle is not GYO-reducible**: no vertex is an ear (each
lies in two edges) and no edge is contained in another, so no first
reduction step exists. -/
theorem triangle_not_gyoReducible : ¬ GYOReducible triangleE := by
  rw [triangleE_eq_cycleE]
  exact cycle_not_gyoReducible 0

/-- **The converse witness at the triangle** — the concrete base case:
the triangle hypergraph carries edge relations (the frustrated XOR
triangle of `Ste.TwistedNonvanishing`, read database-theoretically)
that are edge-supported, pairwise consistent, with all three tables
nonempty, yet globally unsolvable.  Combined with
`triangle_not_gyoReducible`, this is the converse BFMY direction at
the smallest non-acyclic scheme. -/
theorem triangle_pairwiseConsistent_not_solvable :
    ¬ GYOReducible triangleE ∧
    ∃ Rel : Fin 3 → (Fin 3 → Bool) → Prop,
      EdgeSupported triangleE Rel ∧
      PairwiseConsistent (fun _ => (Set.univ : Set Bool)) triangleE Rel ∧
      (∀ k, ∃ t : Fin 3 → Bool,
        (∀ u, t u ∈ (Set.univ : Set Bool)) ∧ Rel k t) ∧
      ¬ ∃ f : Fin 3 → Bool,
        (∀ u, f u ∈ (Set.univ : Set Bool)) ∧ ∀ k, Rel k f := by
  rw [triangleE_eq_cycleE]
  exact cycle_pairwiseConsistent_not_solvable 0

/-- Sanity: the frustrated triangle instance has an empty global
constraint set — `⋂ = ∅` in decidable, computed form. -/
example : ¬ ∃ f : Fin 3 → Bool, ∀ k, cycleRel 0 (oddParam 0) k f := by
  have h : ¬ ∃ f : Fin 3 → Bool,
      ∀ k : Fin 3, Bool.xor (f k) (f (k + 1)) = oddParam 0 k := by decide
  exact fun ⟨f, hf⟩ => h ⟨f, fun k => hf k⟩

end STE
