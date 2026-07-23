/-
Arc consistency implies backtrack-free solvability on a chain.

Freuder's classical tractability theorem (Freuder, *A Sufficient
Condition for Backtrack-Free Search*, JACM 29(1), 1982;
`freuder1982backtrack`) says: a binary constraint network that is
arc-consistent and whose constraint graph has width 1 (a forest) can be
solved backtrack-free — local consistency plus acyclic structure yields
global solvability.  This file mechanizes the *chain* instance of that
theorem, the simplest acyclic case: variables `Fin (n+1)` in a path,
unary domains `D i : Set α`, and a binary constraint `R i` between each
consecutive pair `i, i+1` (indexed by the edge `i : Fin n`, joining
`i.castSucc` to `i.succ`).

Main notions and results:

* `ChainSolution D R f`: `f` picks a value in every domain and satisfies
  every edge constraint; `chainSet D R` is the set of solutions, and
  `chainSet_eq_feasibilitySet` exhibits it as a `feasibilitySet` in the
  sense of `Ste.Basic` — the chain network is an instance of the
  repo-wide constraint formalism.
* `ForwardConsistent` / `BackwardConsistent` / `ArcConsistent`: every
  value in a domain has a *support* at the next (resp. previous)
  variable; arc consistency is both.
* `ChainSolution.snoc`, `ChainSolution.cons`: the single-edge extension
  lemmas — a solution of the chain minus its last (resp. first) variable
  extends across the remaining edge by any supported value.
* `forwardConsistent_chain_solvable_from`: the greedy left-to-right
  construction.  Forward consistency alone, plus a chosen starting value
  `a ∈ D 0`, produces a global solution through `a` — each step extends
  by the support guaranteed at the frontier, with no backtracking.
* `arcConsistent_chain_solvable` (**the Freuder chain theorem**): a
  nonempty arc-consistent chain has a global solution.  Existence
  actually needs only forward consistency and `(D 0).Nonempty`
  (`forwardConsistent_chain_solvable`); the full arc-consistent
  statement is the faithful classical hypothesis.
* `arcConsistent_backtrackFree`: the backtrack-free content in full —
  *every* value of *every* domain of an arc-consistent chain lies on a
  global solution.  No choice made at any single variable is ever
  retracted: forward supports extend it rightward, backward supports
  extend it leftward.

**The gluing reading.**  `Ste.VariablePresheaf` showed that variable-side
gluing of local sections holds for rectangular constraints and fails at
the coupling `diagonal`: singleton sections carry too little data.  The
chain theorem locates the tractable middle ground: take as cover not the
singletons but the *edges* `{i, i+1}`.  An edge's local sections are
`edgeSections D R i ⊆ α × α`, and arc consistency is exactly the
statement that the vertex data is covered by the edge data —
`forwardConsistent_iff_fst`/`backwardConsistent_iff_snd`: every domain
value is a projection of an edge section.  Consecutive edges overlap in
one variable, and `arcConsistent_backtrackFree` is then the gluing
theorem for this cover: locally consistent edge data glues to a global
section, *because the nerve of the edge cover of a path is acyclic*.
The obstruction of `diagonal_gluing_fails` cannot occur.  Wiring this
through the `localSections` presheaf of `Ste.VariablePresheaf` verbatim
(edges as `Set (Fin (n+1))`, sections as dependent functions) is left as
outlook; here the edge sections are kept concrete in `α × α`.

**Honest scope.**  Only the chain (path) case of Freuder's theorem is
mechanized.  NOT formalized here: general forests/trees (width-1 graphs
with branching), the width-`k` / strong-`(k+1)`-consistency hierarchy,
and the statement that every consistent *partial prefix* assignment
extends (we prove extension of every single-variable assignment, which
on a chain is the induction workhorse).  These remain outlook.

Reference: E. C. Freuder, JACM 29(1):24–32, 1982 (`freuder1982backtrack`);
R. Dechter, *Constraint Processing*, 2003, ch. 3–4.
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Ste.Basic

namespace STE

open Set

variable {α : Type*}

/-! ### The chain network -/

/-- A **solution of the chain network**: `f` selects a value in every
domain and satisfies every consecutive binary constraint.  Edge
`i : Fin n` joins variable `i.castSucc` to variable `i.succ`. -/
def ChainSolution {n : ℕ} (D : Fin (n + 1) → Set α)
    (R : Fin n → α → α → Prop) (f : Fin (n + 1) → α) : Prop :=
  (∀ i, f i ∈ D i) ∧ ∀ i : Fin n, R i (f i.castSucc) (f i.succ)

/-- The set of solutions of the chain network. -/
def chainSet {n : ℕ} (D : Fin (n + 1) → Set α)
    (R : Fin n → α → α → Prop) : Set (Fin (n + 1) → α) :=
  {f | ChainSolution D R f}

theorem mem_chainSet {n : ℕ} {D : Fin (n + 1) → Set α}
    {R : Fin n → α → α → Prop} {f : Fin (n + 1) → α} :
    f ∈ chainSet D R ↔ ChainSolution D R f :=
  Iff.rfl

/-- The chain's constraints as an indexed family on assignment space:
one unary constraint per variable, one binary constraint per edge. -/
def chainConstraints {n : ℕ} (D : Fin (n + 1) → Set α)
    (R : Fin n → α → α → Prop) :
    Fin (n + 1) ⊕ Fin n → Set (Fin (n + 1) → α)
  | .inl v => {f | f v ∈ D v}
  | .inr e => {f | R e (f e.castSucc) (f e.succ)}

/-- **The chain is an instance of the repo-wide formalism**: its
solution set is the `feasibilitySet` of the family of unary and binary
constraints. -/
theorem chainSet_eq_feasibilitySet {n : ℕ} (D : Fin (n + 1) → Set α)
    (R : Fin n → α → α → Prop) :
    chainSet D R = feasibilitySet (chainConstraints D R) := by
  ext f
  rw [mem_chainSet, mem_feasibilitySet]
  constructor
  · rintro ⟨hD, hR⟩ (v | e)
    · exact hD v
    · exact hR e
  · intro h
    exact ⟨fun v => h (.inl v), fun e => h (.inr e)⟩

/-! ### Arc consistency -/

/-- **Forward arc consistency**: every value in a domain has a
*support* at the next variable — some value of `D i.succ` compatible
with it under the edge constraint. -/
def ForwardConsistent {n : ℕ} (D : Fin (n + 1) → Set α)
    (R : Fin n → α → α → Prop) : Prop :=
  ∀ i : Fin n, ∀ a ∈ D i.castSucc, ∃ b ∈ D i.succ, R i a b

/-- **Backward arc consistency**: every value in a domain has a support
at the previous variable. -/
def BackwardConsistent {n : ℕ} (D : Fin (n + 1) → Set α)
    (R : Fin n → α → α → Prop) : Prop :=
  ∀ i : Fin n, ∀ b ∈ D i.succ, ∃ a ∈ D i.castSucc, R i a b

/-- **Arc consistency** of the chain: supports in both directions —
every arc of the network, in either orientation, is consistent. -/
def ArcConsistent {n : ℕ} (D : Fin (n + 1) → Set α)
    (R : Fin n → α → α → Prop) : Prop :=
  ForwardConsistent D R ∧ BackwardConsistent D R

/-! ### The edge sections and the gluing reading of arc consistency -/

/-- **The local sections over an edge** `{i, i+1}` of the chain: the
pairs of domain values satisfying the edge constraint — the concrete
(`α × α`-valued) form of the two-variable local sections of the chain
network over the edge cover. -/
def edgeSections {n : ℕ} (D : Fin (n + 1) → Set α)
    (R : Fin n → α → α → Prop) (i : Fin n) : Set (α × α) :=
  {p | p.1 ∈ D i.castSucc ∧ p.2 ∈ D i.succ ∧ R i p.1 p.2}

/-- **Gluing reading, forward direction**: forward arc consistency says
exactly that every vertex value is the first projection of an edge
section — the unary data over `{i}` is covered by the binary data over
`{i, i+1}`. -/
theorem forwardConsistent_iff_fst {n : ℕ} {D : Fin (n + 1) → Set α}
    {R : Fin n → α → α → Prop} :
    ForwardConsistent D R ↔
      ∀ i : Fin n, D i.castSucc ⊆ Prod.fst '' edgeSections D R i := by
  constructor
  · intro h i a ha
    obtain ⟨b, hb, hab⟩ := h i a ha
    exact ⟨(a, b), ⟨ha, hb, hab⟩, rfl⟩
  · intro h i a ha
    obtain ⟨p, hp, rfl⟩ := h i ha
    exact ⟨p.2, hp.2.1, hp.2.2⟩

/-- **Gluing reading, backward direction**: backward arc consistency
says every vertex value is the second projection of an edge section. -/
theorem backwardConsistent_iff_snd {n : ℕ} {D : Fin (n + 1) → Set α}
    {R : Fin n → α → α → Prop} :
    BackwardConsistent D R ↔
      ∀ i : Fin n, D i.succ ⊆ Prod.snd '' edgeSections D R i := by
  constructor
  · intro h i b hb
    obtain ⟨a, ha, hab⟩ := h i b hb
    exact ⟨(a, b), ⟨ha, hb, hab⟩, rfl⟩
  · intro h i b hb
    obtain ⟨p, hp, rfl⟩ := h i hb
    exact ⟨p.1, hp.1, hp.2.2⟩

/-! ### Single-edge extension lemmas -/

/-- **Single-edge extension, right.**  A solution of the chain minus
its last variable extends across the final edge by any value of the
last domain supporting the current frontier value. -/
theorem ChainSolution.snoc {n : ℕ} {D : Fin (n + 2) → Set α}
    {R : Fin (n + 1) → α → α → Prop} {f : Fin (n + 1) → α}
    (hf : ChainSolution (fun i => D i.castSucc) (fun j => R j.castSucc) f)
    {b : α} (hb : b ∈ D (Fin.last (n + 1)))
    (hR : R (Fin.last n) (f (Fin.last n)) b) :
    ChainSolution D R (Fin.snoc f b) := by
  constructor
  · intro i
    cases i using Fin.lastCases with
    | last => rw [Fin.snoc_last]; exact hb
    | cast j => rw [Fin.snoc_castSucc]; exact hf.1 j
  · intro i
    cases i using Fin.lastCases with
    | last =>
      simp only [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]
      exact hR
    | cast j =>
      simp only [Fin.succ_castSucc, Fin.snoc_castSucc]
      exact hf.2 j

/-- **Single-edge extension, left.**  A solution of the chain minus its
first variable extends across the initial edge by any value of the
first domain supported by the current frontier value. -/
theorem ChainSolution.cons {n : ℕ} {D : Fin (n + 2) → Set α}
    {R : Fin (n + 1) → α → α → Prop} {f : Fin (n + 1) → α}
    (hf : ChainSolution (fun i => D i.succ) (fun j => R j.succ) f)
    {a : α} (ha : a ∈ D 0) (hR : R 0 a (f 0)) :
    ChainSolution D R (Fin.cons a f) := by
  constructor
  · intro i
    cases i using Fin.cases with
    | zero => rw [Fin.cons_zero]; exact ha
    | succ j => rw [Fin.cons_succ]; exact hf.1 j
  · intro i
    cases i using Fin.cases with
    | zero =>
      rw [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]
      exact hR
    | succ j =>
      rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
      exact hf.2 j

/-! ### The greedy construction: forward consistency solves the chain -/

/-- **The greedy left-to-right construction.**  On a forward-consistent
chain, any starting value `a ∈ D 0` extends to a global solution through
`a`: each step appends the support guaranteed by forward consistency at
the frontier edge, and no step is ever retracted.  This is the
backtrack-free search of `freuder1982backtrack` on the width-1
(chain-ordered) network. -/
theorem forwardConsistent_chain_solvable_from :
    ∀ {n : ℕ} (D : Fin (n + 1) → Set α) (R : Fin n → α → α → Prop),
      ForwardConsistent D R → ∀ a ∈ D 0,
        ∃ f, ChainSolution D R f ∧ f 0 = a := by
  intro n
  induction n with
  | zero =>
    intro D R _ a ha
    refine ⟨fun _ => a, ⟨fun i => ?_, fun i => i.elim0⟩, rfl⟩
    rw [Fin.eq_zero i]
    exact ha
  | succ m ih =>
    intro D R hFC a ha
    -- forward consistency restricts to the chain minus its last variable
    have hFC' : ForwardConsistent (fun i : Fin (m + 1) => D i.castSucc)
        (fun j : Fin m => R j.castSucc) := by
      intro j c hc
      obtain ⟨b, hb, hRb⟩ := hFC j.castSucc c hc
      rw [Fin.succ_castSucc] at hb
      exact ⟨b, hb, hRb⟩
    have ha' : a ∈ D ((0 : Fin (m + 1)).castSucc) := by
      rw [Fin.castSucc_zero]; exact ha
    -- greedy solution of the truncated chain, through `a`
    obtain ⟨f, hf, hf0⟩ :=
      ih (fun i => D i.castSucc) (fun j => R j.castSucc) hFC' a ha'
    -- the support at the frontier edge extends it
    obtain ⟨b, hb, hRb⟩ := hFC (Fin.last m) (f (Fin.last m)) (hf.1 (Fin.last m))
    rw [Fin.succ_last] at hb
    refine ⟨Fin.snoc f b, hf.snoc hb hRb, ?_⟩
    rw [show (0 : Fin (m + 2)) = (0 : Fin (m + 1)).castSucc by
      rw [Fin.castSucc_zero], Fin.snoc_castSucc]
    exact hf0

/-- **Forward consistency suffices for existence**: a forward-consistent
chain whose first domain is nonempty has a global solution.  (Backward
consistency is not needed for bare existence — only for the full
backtrack-free statement `arcConsistent_backtrackFree`.) -/
theorem forwardConsistent_chain_solvable {n : ℕ}
    {D : Fin (n + 1) → Set α} {R : Fin n → α → α → Prop}
    (hFC : ForwardConsistent D R) (h0 : (D 0).Nonempty) :
    ∃ f, ChainSolution D R f := by
  obtain ⟨a, ha⟩ := h0
  obtain ⟨f, hf, -⟩ := forwardConsistent_chain_solvable_from D R hFC a ha
  exact ⟨f, hf⟩

/-- **Freuder's theorem, chain case** (`freuder1982backtrack`): a
nonempty arc-consistent chain network admits a global solution — a
selection `f` with `f i ∈ D i` for every variable and
`R i (f i.castSucc) (f i.succ)` across every edge.  Local (arc)
consistency plus acyclic (width-1) structure yields global
solvability. -/
theorem arcConsistent_chain_solvable {n : ℕ}
    {D : Fin (n + 1) → Set α} {R : Fin n → α → α → Prop}
    (hAC : ArcConsistent D R) (hne : ∀ i, (D i).Nonempty) :
    ∃ f : Fin (n + 1) → α,
      (∀ i, f i ∈ D i) ∧ ∀ i : Fin n, R i (f i.castSucc) (f i.succ) :=
  forwardConsistent_chain_solvable hAC.1 (hne 0)

/-- The solution set of a nonempty arc-consistent chain is nonempty —
the `feasibilitySet` form of `arcConsistent_chain_solvable`. -/
theorem chainSet_nonempty {n : ℕ} {D : Fin (n + 1) → Set α}
    {R : Fin n → α → α → Prop} (hAC : ArcConsistent D R)
    (hne : ∀ i, (D i).Nonempty) : (chainSet D R).Nonempty :=
  arcConsistent_chain_solvable hAC hne

/-! ### The full backtrack-free statement -/

/-- **Backtrack-free search on the chain**: on an arc-consistent chain,
*every* value of *every* domain lies on a global solution.  The chosen
value is extended rightward by forward supports and leftward by backward
supports, and no choice is ever retracted — the defining property of
backtrack-free search in `freuder1982backtrack`. -/
theorem arcConsistent_backtrackFree :
    ∀ {n : ℕ} (D : Fin (n + 1) → Set α) (R : Fin n → α → α → Prop),
      ArcConsistent D R → ∀ (i₀ : Fin (n + 1)), ∀ a ∈ D i₀,
        ∃ f, ChainSolution D R f ∧ f i₀ = a := by
  intro n
  induction n with
  | zero =>
    intro D R _ i₀ a ha
    refine ⟨fun _ => a, ⟨fun i => ?_, fun i => i.elim0⟩, rfl⟩
    rw [Fin.eq_zero i, ← Fin.eq_zero i₀]
    exact ha
  | succ m ih =>
    intro D R hAC i₀ a ha
    rcases Fin.eq_zero_or_eq_succ i₀ with rfl | ⟨j, rfl⟩
    · -- prescribed value at the first variable: greedy forward suffices
      exact forwardConsistent_chain_solvable_from D R hAC.1 a ha
    · -- prescribed value further right: solve the tail chain through it,
      -- then extend leftward by a backward support
      have hAC' : ArcConsistent (fun i : Fin (m + 1) => D i.succ)
          (fun j' : Fin m => R j'.succ) := by
        constructor
        · intro j' c hc
          have hc' : c ∈ D (j'.castSucc.succ) := hc
          rw [Fin.succ_castSucc] at hc'
          obtain ⟨b, hb, hRb⟩ := hAC.1 j'.succ c hc'
          exact ⟨b, hb, hRb⟩
        · intro j' b hb
          obtain ⟨c, hc, hRc⟩ := hAC.2 j'.succ b hb
          rw [← Fin.succ_castSucc] at hc
          exact ⟨c, hc, hRc⟩
      obtain ⟨g, hg, hgj⟩ := ih (fun i => D i.succ) (fun j' => R j'.succ) hAC' j a ha
      -- backward support at the initial edge
      obtain ⟨a₀, ha₀, hRa₀⟩ := hAC.2 0 (g 0) (hg.1 0)
      rw [Fin.castSucc_zero] at ha₀
      refine ⟨Fin.cons a₀ g, hg.cons ha₀ hRa₀, ?_⟩
      rw [Fin.cons_succ]
      exact hgj

end STE
