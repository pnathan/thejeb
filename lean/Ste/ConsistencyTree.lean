/-
Directional arc consistency solves rooted trees backtrack-free — the
full acyclic (width-1) case of Freuder's theorem.

`Ste.Consistency` mechanized the *chain* instance of Freuder's classical
tractability theorem (Freuder, *A Sufficient Condition for
Backtrack-Free Search*, JACM 29(1), 1982; `freuder1982backtrack`): an
arc-consistent binary network whose constraint graph is a path can be
solved greedily.  Freuder's actual theorem covers every width-1 graph —
an arbitrary forest.  This file closes that gap: the constraint graph is
now a ROOTED TREE (indeed, an arbitrary rooted forest).

**The tree model.**  Nodes are `Fin (n + 1)` with node `0` the root.
Each non-root node `i.succ` (for `i : Fin n`) has a parent `parent i`,
subject to the topological-order hypothesis
`hpar : ∀ i, (parent i).val ≤ i.val`: every node's parent has a strictly
smaller index than the node itself (`(parent i).val ≤ i.val < i.succ.val`),
so processing nodes in increasing index order visits each parent before
its children.  Any rooted forest admits such a numbering (any
topological order of the parent relation), and conversely any `parent`
function satisfying `hpar` is a rooted forest on the index set — the
model captures exactly the acyclic width-1 networks in a fixed
elimination order.  Each edge `i : Fin n` carries a binary constraint
`R i` between the parent's value and the child's value; domains are
`D i : Set α` as in the chain file.

Main notions and results:

* `TreeSolution D parent R f`: `f` picks a value in every domain and
  satisfies every edge constraint; `treeSet` is the solution set and
  `treeSet_eq_feasibilitySet` exhibits it as a `feasibilitySet` of
  `Ste.Basic` — the tree network is an instance of the repo-wide
  constraint formalism.
* `TreeArcConsistent`: **directional arc consistency** along the
  parent→child orientation — every value in a parent's domain has a
  *support* in each child's domain.  This is Freuder's directional
  (ordered) arc consistency for the chosen topological order; on a chain
  it is literally `ForwardConsistent` (`treeArcConsistent_castSucc_iff`).
* `TreeSolution.snoc`: the single-edge extension lemma — a solution of
  the tree minus its last node extends across the final edge by any
  value supported at the (already assigned) parent of the last node.
  The hypothesis `hpar` is what makes this truncation well-formed: the
  last node is a leaf in index order (it is never anyone's parent), and
  its parent survives in the truncated tree.
* `treeArcConsistent_solvable_from` (**backtrack-free search on the
  tree**): directional arc consistency plus a chosen root value
  `a ∈ D 0` produces a global solution through `a`.  The construction
  assigns nodes in increasing index order; each node `i.succ` receives
  the support guaranteed for the already-assigned value of `parent i`,
  and no assignment is ever retracted.  This is the greedy search of
  `freuder1982backtrack` on an arbitrary width-1 (tree-ordered) network,
  and simultaneously the backtrack-free statement for the root: *every*
  root value extends to a global solution.
* `treeArcConsistent_solvable` (**Freuder's theorem, tree case**): a
  nonempty directionally-arc-consistent tree has a global solution.
  Existence needs only the root domain nonempty
  (`treeArcConsistent_solvable_of_root`).
* `treeSolution_castSucc_iff` / `treeArcConsistent_castSucc_iff` /
  `forwardConsistent_chain_solvable_from'`: the chain is the special
  case `parent i = i.castSucc` — the definitions coincide judgmentally,
  and the chain theorem of `Ste.Consistency` re-derives from the tree
  theorem in one line.

**Honest scope.**  Directional arc consistency here is oriented
parent→child only, which suffices for existence and root-value
extension.  The full backtrack-free statement of the chain file
(`arcConsistent_backtrackFree`: *every* value of *every* node lies on a
solution) needs child→parent supports as well and is NOT proven here for
trees; likewise the width-`k` hierarchy remains outlook, as in
`Ste.Consistency`.

Reference: E. C. Freuder, JACM 29(1):24–32, 1982 (`freuder1982backtrack`);
R. Dechter, *Constraint Processing*, 2003, ch. 3–4.
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Ste.Basic
import Ste.Consistency

namespace STE

open Set

variable {α : Type*}

/-! ### The rooted-tree network -/

/-- A **solution of the tree network**: `f` selects a value in every
domain and satisfies every parent–child constraint.  Edge `i : Fin n`
joins the non-root node `i.succ` to its parent `parent i`. -/
def TreeSolution {n : ℕ} (D : Fin (n + 1) → Set α)
    (parent : Fin n → Fin (n + 1)) (R : Fin n → α → α → Prop)
    (f : Fin (n + 1) → α) : Prop :=
  (∀ i, f i ∈ D i) ∧ ∀ i : Fin n, R i (f (parent i)) (f i.succ)

/-- The set of solutions of the tree network. -/
def treeSet {n : ℕ} (D : Fin (n + 1) → Set α)
    (parent : Fin n → Fin (n + 1)) (R : Fin n → α → α → Prop) :
    Set (Fin (n + 1) → α) :=
  {f | TreeSolution D parent R f}

theorem mem_treeSet {n : ℕ} {D : Fin (n + 1) → Set α}
    {parent : Fin n → Fin (n + 1)} {R : Fin n → α → α → Prop}
    {f : Fin (n + 1) → α} :
    f ∈ treeSet D parent R ↔ TreeSolution D parent R f :=
  Iff.rfl

/-- The tree's constraints as an indexed family on assignment space:
one unary constraint per node, one binary constraint per edge. -/
def treeConstraints {n : ℕ} (D : Fin (n + 1) → Set α)
    (parent : Fin n → Fin (n + 1)) (R : Fin n → α → α → Prop) :
    Fin (n + 1) ⊕ Fin n → Set (Fin (n + 1) → α)
  | .inl v => {f | f v ∈ D v}
  | .inr e => {f | R e (f (parent e)) (f e.succ)}

/-- **The tree is an instance of the repo-wide formalism**: its solution
set is the `feasibilitySet` of the family of unary and binary
constraints. -/
theorem treeSet_eq_feasibilitySet {n : ℕ} (D : Fin (n + 1) → Set α)
    (parent : Fin n → Fin (n + 1)) (R : Fin n → α → α → Prop) :
    treeSet D parent R = feasibilitySet (treeConstraints D parent R) := by
  ext f
  rw [mem_treeSet, mem_feasibilitySet]
  constructor
  · rintro ⟨hD, hR⟩ (v | e)
    · exact hD v
    · exact hR e
  · intro h
    exact ⟨fun v => h (.inl v), fun e => h (.inr e)⟩

/-! ### Directional arc consistency -/

/-- **Directional arc consistency** along the parent→child orientation:
every value in a parent's domain has a *support* in the child's domain —
some value of `D i.succ` compatible with it under the edge constraint.
This is Freuder's directional arc consistency for the topological
(index) order of the rooted tree; on the chain
(`parent i = i.castSucc`) it is literally `ForwardConsistent`
(`treeArcConsistent_castSucc_iff`). -/
def TreeArcConsistent {n : ℕ} (D : Fin (n + 1) → Set α)
    (parent : Fin n → Fin (n + 1)) (R : Fin n → α → α → Prop) : Prop :=
  ∀ i : Fin n, ∀ a ∈ D (parent i), ∃ c ∈ D i.succ, R i a c

/-! ### Truncation: removing the last node

The topological-order hypothesis `hpar : ∀ i, (parent i).val ≤ i.val`
makes the last node a leaf in index order: it is never anyone's parent,
so deleting it leaves a well-formed rooted tree on `Fin (m + 1)`, and
every remaining edge's parent index is unchanged. -/

/-- The parent function of the truncated tree: edge `j : Fin m` of the
truncated tree is edge `j.castSucc` of the full tree, whose parent index
is `≤ j < m + 1` by `hpar`, hence a node of the truncated tree. -/
def truncParent {m : ℕ} (parent : Fin (m + 1) → Fin (m + 2))
    (hpar : ∀ i, (parent i).val ≤ i.val) (j : Fin m) : Fin (m + 1) :=
  ⟨(parent j.castSucc).val, by
    have h1 : (parent j.castSucc).val ≤ j.val := by simpa using hpar j.castSucc
    have h2 := j.isLt
    omega⟩

/-- The truncated parent is the original parent, viewed in the full
index set. -/
theorem castSucc_truncParent {m : ℕ} (parent : Fin (m + 1) → Fin (m + 2))
    (hpar : ∀ i, (parent i).val ≤ i.val) (j : Fin m) :
    (truncParent parent hpar j).castSucc = parent j.castSucc := by
  apply Fin.ext
  simp [truncParent]

/-- The truncated tree again satisfies the topological-order
hypothesis. -/
theorem truncParent_le {m : ℕ} (parent : Fin (m + 1) → Fin (m + 2))
    (hpar : ∀ i, (parent i).val ≤ i.val) (j : Fin m) :
    (truncParent parent hpar j).val ≤ j.val := by
  simpa [truncParent] using hpar j.castSucc

/-! ### The single-edge extension lemma -/

/-- **Single-edge extension.**  A solution of the tree minus its last
node extends across the final edge by any value of the last domain
supporting the already-assigned value at the last node's parent.
`parent'` is any parent function agreeing with `parent` on the truncated
tree (`hpp`), and `p` is the last node's parent viewed in the truncated
index set (`hp`). -/
theorem TreeSolution.snoc {m : ℕ} {D : Fin (m + 2) → Set α}
    {parent : Fin (m + 1) → Fin (m + 2)} {R : Fin (m + 1) → α → α → Prop}
    {parent' : Fin m → Fin (m + 1)}
    (hpp : ∀ j : Fin m, (parent' j).castSucc = parent j.castSucc)
    {g : Fin (m + 1) → α}
    (hg : TreeSolution (fun i => D i.castSucc) parent'
      (fun j => R j.castSucc) g)
    {p : Fin (m + 1)} (hp : p.castSucc = parent (Fin.last m))
    {c : α} (hc : c ∈ D (Fin.last (m + 1)))
    (hR : R (Fin.last m) (g p) c) :
    TreeSolution D parent R (Fin.snoc g c) := by
  constructor
  · intro i
    cases i using Fin.lastCases with
    | last => rw [Fin.snoc_last]; exact hc
    | cast j => rw [Fin.snoc_castSucc]; exact hg.1 j
  · intro i
    cases i using Fin.lastCases with
    | last =>
      rw [Fin.succ_last, Fin.snoc_last, ← hp, Fin.snoc_castSucc]
      exact hR
    | cast j =>
      rw [← hpp j, Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
      exact hg.2 j

/-! ### Backtrack-free search on the tree -/

/-- **Backtrack-free search on the tree** (`freuder1982backtrack`).  On
a directionally-arc-consistent rooted tree, any root value `a ∈ D 0`
extends to a global solution through `a`.  The construction assigns
nodes in increasing index order — each node `i.succ` is assigned after
its parent `parent i` (as `(parent i).val ≤ i.val < i.succ.val`), and
directional arc consistency supplies a child value supporting the
already-assigned parent value; no assignment is ever retracted.  In
particular *every* root value lies on a global solution: the
backtrack-free property at the root. -/
theorem treeArcConsistent_solvable_from :
    ∀ {n : ℕ} (D : Fin (n + 1) → Set α) (parent : Fin n → Fin (n + 1))
      (R : Fin n → α → α → Prop),
      (∀ i, (parent i).val ≤ i.val) →
      TreeArcConsistent D parent R → ∀ a ∈ D 0,
        ∃ f, TreeSolution D parent R f ∧ f 0 = a := by
  intro n
  induction n with
  | zero =>
    intro D parent R _ _ a ha
    refine ⟨fun _ => a, ⟨fun i => ?_, fun i => i.elim0⟩, rfl⟩
    rw [Fin.eq_zero i]
    exact ha
  | succ m ih =>
    intro D parent R hpar hAC a ha
    -- directional arc consistency restricts to the tree minus its last
    -- node (a leaf in index order, by `hpar`)
    have hAC' : TreeArcConsistent (fun i : Fin (m + 1) => D i.castSucc)
        (truncParent parent hpar) (fun j : Fin m => R j.castSucc) := by
      intro j b hb
      have hb' : b ∈ D (parent j.castSucc) := by
        rw [← castSucc_truncParent parent hpar j]
        exact hb
      obtain ⟨c, hc, hRc⟩ := hAC j.castSucc b hb'
      rw [Fin.succ_castSucc] at hc
      exact ⟨c, hc, hRc⟩
    have ha' : a ∈ D ((0 : Fin (m + 1)).castSucc) := by
      rw [Fin.castSucc_zero]; exact ha
    -- backtrack-free solution of the truncated tree, through `a`
    obtain ⟨g, hg, hg0⟩ :=
      ih (fun i => D i.castSucc) (truncParent parent hpar)
        (fun j => R j.castSucc) (truncParent_le parent hpar) hAC' a ha'
    -- the last node's parent is a node of the truncated tree, hence
    -- already assigned
    have hlt : (parent (Fin.last m)).val < m + 1 := by
      have h1 : (parent (Fin.last m)).val ≤ m := by
        simpa using hpar (Fin.last m)
      omega
    obtain ⟨q, hq⟩ : ∃ q : Fin (m + 1), q.castSucc = parent (Fin.last m) :=
      ⟨⟨(parent (Fin.last m)).val, hlt⟩, Fin.ext (by simp)⟩
    have hgq : g q ∈ D (parent (Fin.last m)) := by
      rw [← hq]
      exact hg.1 q
    -- the support at the final edge extends the truncated solution
    obtain ⟨c, hc, hRc⟩ := hAC (Fin.last m) (g q) hgq
    rw [Fin.succ_last] at hc
    refine ⟨Fin.snoc g c,
      hg.snoc (castSucc_truncParent parent hpar) hq hc hRc, ?_⟩
    rw [show (0 : Fin (m + 2)) = (0 : Fin (m + 1)).castSucc by
      rw [Fin.castSucc_zero], Fin.snoc_castSucc]
    exact hg0

/-- **Root nonemptiness suffices for existence**: a
directionally-arc-consistent tree whose root domain is nonempty has a
global solution. -/
theorem treeArcConsistent_solvable_of_root {n : ℕ}
    {D : Fin (n + 1) → Set α} {parent : Fin n → Fin (n + 1)}
    {R : Fin n → α → α → Prop}
    (hpar : ∀ i, (parent i).val ≤ i.val)
    (hAC : TreeArcConsistent D parent R) (h0 : (D 0).Nonempty) :
    ∃ f, TreeSolution D parent R f := by
  obtain ⟨a, ha⟩ := h0
  obtain ⟨f, hf, -⟩ :=
    treeArcConsistent_solvable_from D parent R hpar hAC a ha
  exact ⟨f, hf⟩

/-- **Freuder's theorem, tree case** (`freuder1982backtrack`): a
nonempty directionally-arc-consistent rooted tree network admits a
global solution — a selection `f` with `f i ∈ D i` for every node and
`R i (f (parent i)) (f i.succ)` across every parent–child edge.  Local
(directional arc) consistency plus acyclic (width-1) structure yields
global solvability — the full acyclic case, generalizing the chain
theorem `arcConsistent_chain_solvable` of `Ste.Consistency`. -/
theorem treeArcConsistent_solvable {n : ℕ}
    {D : Fin (n + 1) → Set α} {parent : Fin n → Fin (n + 1)}
    {R : Fin n → α → α → Prop}
    (hpar : ∀ i, (parent i).val ≤ i.val)
    (hAC : TreeArcConsistent D parent R) (hne : ∀ i, (D i).Nonempty) :
    ∃ f : Fin (n + 1) → α,
      (∀ i, f i ∈ D i) ∧ ∀ i : Fin n, R i (f (parent i)) (f i.succ) :=
  treeArcConsistent_solvable_of_root hpar hAC (hne 0)

/-- The solution set of a nonempty directionally-arc-consistent tree is
nonempty — the `feasibilitySet` form of `treeArcConsistent_solvable`. -/
theorem treeSet_nonempty {n : ℕ} {D : Fin (n + 1) → Set α}
    {parent : Fin n → Fin (n + 1)} {R : Fin n → α → α → Prop}
    (hpar : ∀ i, (parent i).val ≤ i.val)
    (hAC : TreeArcConsistent D parent R) (hne : ∀ i, (D i).Nonempty) :
    (treeSet D parent R).Nonempty :=
  treeArcConsistent_solvable hpar hAC hne

/-! ### The chain as a special case

Taking `parent i = i.castSucc` — every node's parent is its immediate
predecessor — the rooted tree is the path, and the tree notions
coincide judgmentally with the chain notions of `Ste.Consistency`. -/

/-- On the path (`parent i = i.castSucc`), a tree solution is exactly a
chain solution. -/
theorem treeSolution_castSucc_iff {n : ℕ} (D : Fin (n + 1) → Set α)
    (R : Fin n → α → α → Prop) (f : Fin (n + 1) → α) :
    TreeSolution D (fun i => i.castSucc) R f ↔ ChainSolution D R f :=
  Iff.rfl

/-- On the path, directional arc consistency is exactly forward
consistency. -/
theorem treeArcConsistent_castSucc_iff {n : ℕ} (D : Fin (n + 1) → Set α)
    (R : Fin n → α → α → Prop) :
    TreeArcConsistent D (fun i => i.castSucc) R ↔ ForwardConsistent D R :=
  Iff.rfl

/-- The chain theorem `forwardConsistent_chain_solvable_from` of
`Ste.Consistency` re-derived as the path special case of the tree
theorem. -/
theorem forwardConsistent_chain_solvable_from' {n : ℕ}
    (D : Fin (n + 1) → Set α) (R : Fin n → α → α → Prop)
    (hFC : ForwardConsistent D R) :
    ∀ a ∈ D 0, ∃ f, ChainSolution D R f ∧ f 0 = a :=
  treeArcConsistent_solvable_from D (fun i => i.castSucc) R
    (fun i => le_of_eq (by simp))
    ((treeArcConsistent_castSucc_iff D R).mpr hFC)

end STE
