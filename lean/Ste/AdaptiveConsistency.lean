/-
Adaptive (directional) consistency solves bounded-induced-width networks
backtrack-free — the cyclic / width-k generalization of the tree case.

`Ste.ConsistencyTree` mechanized the width-1 instance of Freuder's
classical tractability theorem (`freuder1982backtrack`): a directionally
arc-consistent TREE is solved greedily, no backtracking.  There every
non-root node `i.succ` had a SINGLE earlier neighbour `parent i`.  This
file removes the single-parent restriction: node `i.succ` now carries a
whole SEPARATOR `sep i : Finset (Fin (n + 1))` of earlier neighbours —
the parent set of the node in the induced (fill-in) graph of an
elimination order — and one BUCKET constraint `R i` that reads exactly
the coordinates `sep i ∪ {i.succ}`.

**Why this is the cyclic case.**  A constraint CYCLE numbered along any
elimination order necessarily produces a node with TWO earlier
neighbours (close the cycle: the last node of the cycle sees both the
next-to-last node and, through the chord created by elimination, the
first).  Width 1 (`|sep i| ≤ 1`, `sepWidthLE_singleton`) is exactly the
forest case of `Ste.ConsistencyTree`; `|sep i| ≥ 2` is what cyclic
primal graphs generate, and `w = max |sep i|` is the INDUCED WIDTH
(treewidth along the chosen order) of the network.  Directional
consistency of the buckets — Dechter's adaptive consistency, Freuder's
strong (w+1)-consistency restricted to the order — then yields a
backtrack-free solution, for ANY induced width.  This is the
`k ≥ 2` / cyclic generalization left as outlook in `Ste.Consistency`
and `Ste.ConsistencyTree`.

**The model.**  Nodes `Fin (n + 1)`, domains `D u : Set α`.  For each
`i : Fin n` the bucket of node `i.succ` consists of

* a separator `sep i : Finset (Fin (n + 1))` with
  `hsep : ∀ u ∈ sep i, u.val ≤ i.val` — all separator members precede
  `i.succ` (topological / elimination numbering), and
* a bucket constraint `R i : (Fin (n + 1) → α) → Prop` together with the
  dependence hypothesis `SepSupported sep R`: `R i` gives the same
  verdict on assignments that agree on `sep i` and at `i.succ` — the
  constraint genuinely has scope `sep i ∪ {i.succ}`.

Main notions and results:

* `AdaptiveSolution D R f`: `f` picks a value in every domain and
  satisfies every bucket constraint; `adaptiveSet` is the solution set
  and `adaptiveSet_eq_feasibilitySet` exhibits it as a `feasibilitySet`
  of `Ste.Basic` — the bucket network is an instance of the repo-wide
  constraint formalism.
* `DirectionalConsistent D R`: for every domain-respecting assignment
  of the earlier variables, node `i.succ` has a domain value making its
  bucket constraint true.  With `|sep i| ≤ w` this is directional
  (w+1)-consistency along the elimination order — the output condition
  of Dechter's adaptive-consistency algorithm (`dechter2003constraint`,
  ch. 4) and of Freuder's width/consistency theorem
  (`freuder1982backtrack`).
* `PrefixConsistent D R`: the a-priori stronger variant that conditions
  only on the variables up to `i` (later coordinates unconstrained) —
  Dechter's actual definition; `DirectionalConsistent.prefixConsistent`
  recovers it from `DirectionalConsistent` when all domains are
  nonempty, using the dependence hypothesis to discard the junk at the
  later coordinates.
* `prefixConsistent_solvable_from` (the greedy engine): a prefix-
  consistent network extends any root value `a ∈ D 0` to a global
  solution.  Nodes are assigned in increasing index order — all of
  `sep i` precedes `i.succ` by `hsep`, so when `i.succ` is reached its
  separator is fully assigned and consistency hands over a compatible
  value; no assignment is ever retracted.  The induction peels the last
  node `Fin.snoc`-style exactly as in `Ste.ConsistencyTree`; the
  dependence hypothesis (in the derived prefix form `PrefixSupported`)
  is what makes the truncation well-formed: `R i` cannot see the
  deleted last coordinate.
* `directionalConsistent_solvable_from` / `directionalConsistent_solvable`
  (**adaptive-consistency theorem, bounded induced width**): a nonempty
  directionally-consistent bucket network has a global solution, indeed
  one through any prescribed root value.
* Specializations: `treeArcConsistent_solvable_of_adaptive` re-derives
  the tree theorem of `Ste.ConsistencyTree` via `sep i = {parent i}`
  (width 1, `sepWidthLE_singleton`), and `twoParent_solvable` is the
  first properly cyclic instance — two earlier neighbours
  `sep i = {p i, q i}` (width ≤ 2, `sepWidthLE_pair`), which covers
  every triangulated cycle.

**Honest scope.**  (1) `DirectionalConsistent` quantifies over fully
domain-respecting assignments, so an empty later domain makes it
vacuous while destroying solvability; the solvability theorems for it
therefore assume all domains nonempty (`hne`), unlike the tree file
where the root sufficed — with the stronger `PrefixConsistent` the root
value alone suffices (`prefixConsistent_solvable_from`), which is the
faithful analogue of the tree statement.  (2) This file proves the
DECISION/construction half — consistency implies solvability.  That
adaptive consistency can be ENFORCED by bucket elimination in time
exponential only in `w` (the algorithmic half of `dechter2003constraint`)
is not modelled.  (3) Backtrack-freeness is stated at the root; the
"every value of every node" version needs both orientations, as in the
tree file.

References: E. C. Freuder, *A Sufficient Condition for Backtrack-Free
Search*, JACM 29(1):24–32, 1982 (`freuder1982backtrack`); R. Dechter,
*Constraint Processing*, Morgan Kaufmann, 2003, ch. 4 (adaptive
consistency, induced width) (`dechter2003constraint`).
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Ste.Basic
import Ste.ConsistencyTree

namespace STE

open Set

variable {α : Type*}

/-! ### The bucket network -/

/-- A **solution of the bucket network**: `f` selects a value in every
domain and satisfies every bucket constraint.  Bucket `i : Fin n`
belongs to the non-root node `i.succ`; the constraint `R i` reads the
whole assignment but (via `SepSupported`) depends only on the
coordinates `sep i ∪ {i.succ}`. -/
def AdaptiveSolution {n : ℕ} (D : Fin (n + 1) → Set α)
    (R : Fin n → (Fin (n + 1) → α) → Prop) (f : Fin (n + 1) → α) : Prop :=
  (∀ u, f u ∈ D u) ∧ ∀ i : Fin n, R i f

/-- The set of solutions of the bucket network. -/
def adaptiveSet {n : ℕ} (D : Fin (n + 1) → Set α)
    (R : Fin n → (Fin (n + 1) → α) → Prop) : Set (Fin (n + 1) → α) :=
  {f | AdaptiveSolution D R f}

theorem mem_adaptiveSet {n : ℕ} {D : Fin (n + 1) → Set α}
    {R : Fin n → (Fin (n + 1) → α) → Prop} {f : Fin (n + 1) → α} :
    f ∈ adaptiveSet D R ↔ AdaptiveSolution D R f :=
  Iff.rfl

/-- The bucket network's constraints as an indexed family on assignment
space: one unary constraint per node, one bucket constraint per
non-root node. -/
def adaptiveConstraints {n : ℕ} (D : Fin (n + 1) → Set α)
    (R : Fin n → (Fin (n + 1) → α) → Prop) :
    Fin (n + 1) ⊕ Fin n → Set (Fin (n + 1) → α)
  | .inl v => {f | f v ∈ D v}
  | .inr e => {f | R e f}

/-- **The bucket network is an instance of the repo-wide formalism**:
its solution set is the `feasibilitySet` of the family of unary and
bucket constraints. -/
theorem adaptiveSet_eq_feasibilitySet {n : ℕ} (D : Fin (n + 1) → Set α)
    (R : Fin n → (Fin (n + 1) → α) → Prop) :
    adaptiveSet D R = feasibilitySet (adaptiveConstraints D R) := by
  ext f
  rw [mem_adaptiveSet, mem_feasibilitySet]
  constructor
  · rintro ⟨hD, hR⟩ (v | e)
    · exact hD v
    · exact hR e
  · intro h
    exact ⟨fun v => h (.inl v), fun e => h (.inr e)⟩

/-! ### Scope: separator dependence and induced width -/

/-- **Separator dependence**: the bucket constraint `R i` has scope
`sep i ∪ {i.succ}` — it gives the same verdict on any two assignments
that agree on the separator and at the node itself.  This is the clean
formulation of "`R i` is a constraint over the variables
`sep i ∪ {i.succ}`" for constraints presented on whole assignments. -/
def SepSupported {n : ℕ} (sep : Fin n → Finset (Fin (n + 1)))
    (R : Fin n → (Fin (n + 1) → α) → Prop) : Prop :=
  ∀ i : Fin n, ∀ g g' : Fin (n + 1) → α,
    (∀ u ∈ sep i, g u = g' u) → g i.succ = g' i.succ → (R i g ↔ R i g')

/-- **Prefix dependence**: `R i` depends only on the coordinates
`≤ i + 1`.  This is what the greedy induction actually consumes; by
`SepSupported.prefixSupported` it follows from separator dependence
plus the topological-order hypothesis on the separators. -/
def PrefixSupported {n : ℕ} (R : Fin n → (Fin (n + 1) → α) → Prop) : Prop :=
  ∀ i : Fin n, ∀ g g' : Fin (n + 1) → α,
    (∀ u : Fin (n + 1), u.val ≤ i.val + 1 → g u = g' u) → (R i g ↔ R i g')

/-- Separator dependence plus topologically ordered separators
(`∀ u ∈ sep i, u.val ≤ i.val`) yields prefix dependence: everything
`R i` can see lives at coordinates `≤ i + 1`. -/
theorem SepSupported.prefixSupported {n : ℕ}
    {sep : Fin n → Finset (Fin (n + 1))}
    {R : Fin n → (Fin (n + 1) → α) → Prop} (hdep : SepSupported sep R)
    (hsep : ∀ i : Fin n, ∀ u ∈ sep i, u.val ≤ i.val) :
    PrefixSupported R :=
  fun i g g' h =>
    hdep i g g' (fun u hu => h u (le_trans (hsep i u hu) (Nat.le_succ _)))
      (h i.succ (le_of_eq (Fin.val_succ i)))

/-- **Induced-width bound**: every separator has at most `w` members.
`w = 1` is the forest case of `Ste.ConsistencyTree`; `w ≥ 2` is where
cyclic primal graphs live, and in general `w` is the induced width
(treewidth along the elimination order) of the network. -/
def SepWidthLE {n : ℕ} (sep : Fin n → Finset (Fin (n + 1))) (w : ℕ) : Prop :=
  ∀ i, (sep i).card ≤ w

/-- Single-parent separators have induced width 1 — the tree case. -/
theorem sepWidthLE_singleton {n : ℕ} (parent : Fin n → Fin (n + 1)) :
    SepWidthLE (fun i => {parent i}) 1 := by
  intro i
  simp

/-- Two-parent separators have induced width at most 2 — the smallest
properly cyclic case (a cycle eliminated in order gives a node with two
earlier neighbours). -/
theorem sepWidthLE_pair {n : ℕ} (p q : Fin n → Fin (n + 1)) :
    SepWidthLE (fun i => {p i, q i}) 2 := by
  intro i
  show ({p i, q i} : Finset (Fin (n + 1))).card ≤ 2
  have h := Finset.card_insert_le (p i) ({q i} : Finset (Fin (n + 1)))
  simp only [Finset.card_singleton] at h
  omega

/-! ### Directional consistency -/

/-- **Directional consistency** of the buckets along the elimination
order: for every domain-respecting assignment `g`, node `i.succ` has a
domain value `c` making its bucket constraint true once `c` is written
into the assignment.  Since `R i` only reads `sep i ∪ {i.succ}` and
`|sep i| ≤ w`, this is directional (w+1)-consistency — the condition
established by Dechter's adaptive-consistency / bucket-elimination
procedure (`dechter2003constraint`, ch. 4), and the order-restricted
form of Freuder's strong (w+1)-consistency (`freuder1982backtrack`). -/
def DirectionalConsistent {n : ℕ} (D : Fin (n + 1) → Set α)
    (R : Fin n → (Fin (n + 1) → α) → Prop) : Prop :=
  ∀ i : Fin n, ∀ g : Fin (n + 1) → α, (∀ u, g u ∈ D u) →
    ∃ c ∈ D i.succ, R i (Function.update g i.succ c)

/-- **Prefix consistency**: like `DirectionalConsistent`, but the
assignment `g` need respect the domains only at the coordinates `≤ i` —
the variables already assigned when the greedy sweep reaches `i.succ`.
This is Dechter's directional consistency verbatim (consistency
relative to the EARLIER variables); it is the hypothesis the greedy
engine consumes, and it is implied by `DirectionalConsistent` on
nonempty domains (`DirectionalConsistent.prefixConsistent`). -/
def PrefixConsistent {n : ℕ} (D : Fin (n + 1) → Set α)
    (R : Fin n → (Fin (n + 1) → α) → Prop) : Prop :=
  ∀ i : Fin n, ∀ g : Fin (n + 1) → α,
    (∀ u : Fin (n + 1), u.val ≤ i.val → g u ∈ D u) →
    ∃ c ∈ D i.succ, R i (Function.update g i.succ c)

/-- On nonempty domains, directional consistency upgrades to prefix
consistency: pad the unassigned later coordinates with arbitrary domain
values, and use prefix dependence to discard the padding again. -/
theorem DirectionalConsistent.prefixConsistent {n : ℕ}
    {D : Fin (n + 1) → Set α} {R : Fin n → (Fin (n + 1) → α) → Prop}
    (hDC : DirectionalConsistent D R) (hdep : PrefixSupported R)
    (hne : ∀ u, (D u).Nonempty) : PrefixConsistent D R := by
  intro i g hg
  have hg'D : ∀ u : Fin (n + 1),
      (fun u : Fin (n + 1) =>
        if u.val ≤ i.val then g u else (hne u).some) u ∈ D u := by
    intro u
    show (if u.val ≤ i.val then g u else (hne u).some) ∈ D u
    by_cases h : u.val ≤ i.val
    · rw [if_pos h]
      exact hg u h
    · rw [if_neg h]
      exact (hne u).some_mem
  obtain ⟨c, hc, hRc⟩ := hDC i _ hg'D
  refine ⟨c, hc, (hdep i _ _ ?_).mpr hRc⟩
  intro u hu
  by_cases h : u = i.succ
  · subst h
    rw [Function.update_self, Function.update_self]
  · have hu' : u.val ≤ i.val := by
      by_contra hcon
      apply h
      apply Fin.ext
      rw [Fin.val_succ]
      omega
    rw [Function.update_of_ne h, Function.update_of_ne h]
    show g u = if u.val ≤ i.val then g u else (hne u).some
    rw [if_pos hu']

/-! ### Truncation toolkit

Peeling the last node: with prefix dependence no bucket of the
truncated network can see the deleted coordinate, so restricting along
`Fin.snoc` with a junk last value is harmless. -/

/-- Two `snoc` extensions of the same prefix agree strictly below the
last coordinate. -/
theorem snoc_eq_snoc_of_lt {m : ℕ} (g : Fin (m + 1) → α) (b c : α)
    {u : Fin (m + 2)} (hu : u.val < m + 1) :
    Fin.snoc g b u = Fin.snoc g c u := by
  have hu' : u = (⟨u.val, hu⟩ : Fin (m + 1)).castSucc := by
    apply Fin.ext
    simp
  rw [hu', Fin.snoc_castSucc, Fin.snoc_castSucc]

/-! ### Backtrack-free search on the bucket network -/

/-- **The greedy engine** (`freuder1982backtrack`,
`dechter2003constraint`): on a prefix-consistent bucket network, any
root value `a ∈ D 0` extends to a global solution through `a`.  Nodes
are assigned in increasing index order; when node `i.succ` is reached
its separator is already assigned (all members precede it), and prefix
consistency supplies a compatible domain value — no assignment is ever
retracted.  The induction peels the last node as in
`Ste.ConsistencyTree`, with prefix dependence (`hdep`) certifying that
the surviving buckets cannot see the deleted coordinate.  Note that
only the ROOT domain is required nonempty — the faithful analogue of
the tree statement. -/
theorem prefixConsistent_solvable_from :
    ∀ {n : ℕ} (D : Fin (n + 1) → Set α)
      (R : Fin n → (Fin (n + 1) → α) → Prop),
      PrefixSupported R → PrefixConsistent D R →
      ∀ a ∈ D 0, ∃ f, AdaptiveSolution D R f ∧ f 0 = a := by
  intro n
  induction n with
  | zero =>
    intro D R _ _ a ha
    refine ⟨fun _ => a, ⟨fun u => ?_, fun i => i.elim0⟩, rfl⟩
    rw [Fin.eq_zero u]
    exact ha
  | succ m ih =>
    intro D R hdep hPC a ha
    -- prefix dependence restricts to the network minus its last node
    -- (padding the deleted coordinate with the junk value `a`)
    have hdep' : PrefixSupported (fun j (g : Fin (m + 1) → α) =>
        R j.castSucc (Fin.snoc g a)) := by
      intro j g1 g2 hagree
      show R j.castSucc (Fin.snoc g1 a) ↔ R j.castSucc (Fin.snoc g2 a)
      apply hdep j.castSucc
      intro u hu
      have hj := j.isLt
      have hu1 : u.val ≤ j.val + 1 := by simpa using hu
      have hum : u.val < m + 1 := by omega
      have hu' : u = (⟨u.val, hum⟩ : Fin (m + 1)).castSucc := by
        apply Fin.ext
        simp
      rw [hu', Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hagree ⟨u.val, hum⟩ hu1
    -- prefix consistency restricts likewise
    have hPC' : PrefixConsistent (fun u : Fin (m + 1) => D u.castSucc)
        (fun j g => R j.castSucc (Fin.snoc g a)) := by
      intro j g hg
      have hgz : ∀ u : Fin (m + 2), u.val ≤ (j.castSucc).val →
          Fin.snoc g a u ∈ D u := by
        intro u hu
        have hj := j.isLt
        have hum : u.val < m + 1 := by
          simp only [Fin.coe_castSucc] at hu
          omega
        have hu' : u = (⟨u.val, hum⟩ : Fin (m + 1)).castSucc := by
          apply Fin.ext
          simp
        rw [hu', Fin.snoc_castSucc]
        apply hg
        simpa using hu
      obtain ⟨c, hc, hRc⟩ := hPC j.castSucc (Fin.snoc g a) hgz
      rw [Fin.succ_castSucc] at hc hRc
      rw [← Fin.snoc_update] at hRc
      exact ⟨c, hc, hRc⟩
    have ha' : a ∈ D ((0 : Fin (m + 1)).castSucc) := by
      rw [Fin.castSucc_zero]
      exact ha
    -- backtrack-free solution of the truncated network, through `a`
    obtain ⟨g, hg, hg0⟩ :=
      ih (fun u => D u.castSucc) (fun j g => R j.castSucc (Fin.snoc g a))
        hdep' hPC' a ha'
    -- the last node's separator is fully assigned; prefix consistency
    -- hands over a value for the final bucket
    have hgz : ∀ u : Fin (m + 2), u.val ≤ (Fin.last m).val →
        Fin.snoc g a u ∈ D u := by
      intro u hu
      have hum : u.val < m + 1 := by
        simp only [Fin.val_last] at hu
        omega
      have hu' : u = (⟨u.val, hum⟩ : Fin (m + 1)).castSucc := by
        apply Fin.ext
        simp
      rw [hu', Fin.snoc_castSucc]
      exact hg.1 _
    obtain ⟨c, hc, hRc⟩ := hPC (Fin.last m) (Fin.snoc g a) hgz
    rw [Fin.succ_last] at hc hRc
    rw [Fin.update_snoc_last] at hRc
    refine ⟨Fin.snoc g c, ⟨?_, ?_⟩, ?_⟩
    · intro u
      cases u using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact hc
      | cast v => rw [Fin.snoc_castSucc]; exact hg.1 v
    · intro i
      cases i using Fin.lastCases with
      | last => exact hRc
      | cast j =>
        refine (hdep j.castSucc (Fin.snoc g c) (Fin.snoc g a) ?_).mpr
          (hg.2 j)
        intro u hu
        have hj := j.isLt
        have hu1 : u.val ≤ j.val + 1 := by simpa using hu
        have hum : u.val < m + 1 := by omega
        exact snoc_eq_snoc_of_lt g c a hum
    · rw [show (0 : Fin (m + 2)) = (0 : Fin (m + 1)).castSucc by
        rw [Fin.castSucc_zero], Fin.snoc_castSucc]
      exact hg0

/-- **Backtrack-free search, bounded induced width**
(`freuder1982backtrack`; `dechter2003constraint`, ch. 4).  On a
nonempty, directionally-consistent bucket network whose separators are
topologically ordered (`hsep`) and delimit the constraint scopes
(`hdep`), any root value `a ∈ D 0` extends to a global solution through
`a`.  With `SepWidthLE sep w` this is the induced-width-`w` case —
`w = 1` the trees of `Ste.ConsistencyTree`, `w ≥ 2` the cyclic
networks. -/
theorem directionalConsistent_solvable_from {n : ℕ}
    (D : Fin (n + 1) → Set α) (sep : Fin n → Finset (Fin (n + 1)))
    (R : Fin n → (Fin (n + 1) → α) → Prop)
    (hsep : ∀ i : Fin n, ∀ u ∈ sep i, u.val ≤ i.val)
    (hdep : SepSupported sep R)
    (hDC : DirectionalConsistent D R) (hne : ∀ u, (D u).Nonempty) :
    ∀ a ∈ D 0, ∃ f, AdaptiveSolution D R f ∧ f 0 = a :=
  prefixConsistent_solvable_from D R (hdep.prefixSupported hsep)
    (hDC.prefixConsistent (hdep.prefixSupported hsep) hne)

/-- **The adaptive-consistency theorem** (Freuder's width theorem along
an elimination order; `freuder1982backtrack`, `dechter2003constraint`):
a nonempty directionally-consistent bucket network admits a global
solution — a selection `f` with `f u ∈ D u` at every node satisfying
every bucket constraint.  Local (directional, width-bounded)
consistency plus an elimination order with separators of any size
yields global solvability — the cyclic / width-`k` generalization of
the tree theorem `treeArcConsistent_solvable`. -/
theorem directionalConsistent_solvable {n : ℕ}
    {D : Fin (n + 1) → Set α} {sep : Fin n → Finset (Fin (n + 1))}
    {R : Fin n → (Fin (n + 1) → α) → Prop}
    (hsep : ∀ i : Fin n, ∀ u ∈ sep i, u.val ≤ i.val)
    (hdep : SepSupported sep R)
    (hDC : DirectionalConsistent D R) (hne : ∀ u, (D u).Nonempty) :
    ∃ f, AdaptiveSolution D R f := by
  obtain ⟨a, ha⟩ := hne 0
  obtain ⟨f, hf, -⟩ :=
    directionalConsistent_solvable_from D sep R hsep hdep hDC hne a ha
  exact ⟨f, hf⟩

/-- The solution set of a nonempty directionally-consistent bucket
network is nonempty — the `feasibilitySet` form of
`directionalConsistent_solvable`. -/
theorem adaptiveSet_nonempty {n : ℕ} {D : Fin (n + 1) → Set α}
    {sep : Fin n → Finset (Fin (n + 1))}
    {R : Fin n → (Fin (n + 1) → α) → Prop}
    (hsep : ∀ i : Fin n, ∀ u ∈ sep i, u.val ≤ i.val)
    (hdep : SepSupported sep R)
    (hDC : DirectionalConsistent D R) (hne : ∀ u, (D u).Nonempty) :
    (adaptiveSet D R).Nonempty :=
  directionalConsistent_solvable hsep hdep hDC hne

/-! ### The tree as the width-1 special case

`sep i = {parent i}` recovers `Ste.ConsistencyTree`: singleton
separators (`sepWidthLE_singleton`) are exactly the rooted forests, and
directional arc consistency of the tree becomes directional consistency
of the buckets. -/

/-- Directional arc consistency of a rooted tree is directional
consistency of the corresponding single-parent bucket network. -/
theorem treeArcConsistent_directionalConsistent {n : ℕ}
    {D : Fin (n + 1) → Set α} {parent : Fin n → Fin (n + 1)}
    {R : Fin n → α → α → Prop}
    (hpar : ∀ i, (parent i).val ≤ i.val)
    (hAC : TreeArcConsistent D parent R) :
    DirectionalConsistent D (fun i g => R i (g (parent i)) (g i.succ)) := by
  intro i g hg
  obtain ⟨c, hc, hRc⟩ := hAC i (g (parent i)) (hg (parent i))
  have hpne : parent i ≠ i.succ := by
    intro h
    have h1 := hpar i
    rw [h, Fin.val_succ] at h1
    omega
  refine ⟨c, hc, ?_⟩
  show R i (Function.update g i.succ c (parent i))
    (Function.update g i.succ c i.succ)
  rw [Function.update_of_ne hpne, Function.update_self]
  exact hRc

/-- **The tree theorem is subsumed** (width 1): Freuder's tree case of
`Ste.ConsistencyTree` re-derived from the adaptive-consistency theorem
with singleton separators `sep i = {parent i}`. -/
theorem treeArcConsistent_solvable_of_adaptive {n : ℕ}
    {D : Fin (n + 1) → Set α} {parent : Fin n → Fin (n + 1)}
    {R : Fin n → α → α → Prop}
    (hpar : ∀ i, (parent i).val ≤ i.val)
    (hAC : TreeArcConsistent D parent R) (hne : ∀ u, (D u).Nonempty) :
    ∃ f, TreeSolution D parent R f := by
  have hsep : ∀ i : Fin n, ∀ u ∈ ({parent i} : Finset (Fin (n + 1))),
      u.val ≤ i.val := by
    intro i u hu
    rw [Finset.mem_singleton] at hu
    subst hu
    exact hpar i
  have hdep : SepSupported (fun i => ({parent i} : Finset (Fin (n + 1))))
      (fun i g => R i (g (parent i)) (g i.succ)) := by
    intro i g g' hs hsucc
    show R i (g (parent i)) (g i.succ) ↔ R i (g' (parent i)) (g' i.succ)
    rw [hs (parent i) (Finset.mem_singleton_self _), hsucc]
  obtain ⟨f, hf⟩ := directionalConsistent_solvable hsep hdep
    (treeArcConsistent_directionalConsistent hpar hAC) hne
  exact ⟨f, hf.1, hf.2⟩

/-! ### The first properly cyclic case: two earlier neighbours

A node with TWO earlier neighbours is what a cycle produces under any
elimination order (the elimination fill-in closes the cycle into
triangles).  `sep i = {p i, q i}` with a ternary bucket constraint is
therefore the smallest genuinely cyclic — width-2 — instance, out of
reach of the tree formalism. -/

/-- **Backtrack-free search on width-2 (cyclic) networks**: a nonempty
network in which each node `i.succ` has two earlier neighbours
`p i, q i` and a directionally consistent ternary bucket constraint
`R i` admits a global solution.  Instantiating `p`/`q` along a
triangulated cycle solves cyclic constraint graphs — the case
`k = 3` (strong 3-consistency ⇒ width 2 solvable) of
`freuder1982backtrack`. -/
theorem twoParent_solvable {n : ℕ}
    {D : Fin (n + 1) → Set α} {p q : Fin n → Fin (n + 1)}
    {R : Fin n → α → α → α → Prop}
    (hp : ∀ i, (p i).val ≤ i.val) (hq : ∀ i, (q i).val ≤ i.val)
    (hDC : ∀ i : Fin n, ∀ g : Fin (n + 1) → α, (∀ u, g u ∈ D u) →
      ∃ c ∈ D i.succ, R i (g (p i)) (g (q i)) c)
    (hne : ∀ u, (D u).Nonempty) :
    ∃ f : Fin (n + 1) → α, (∀ u, f u ∈ D u) ∧
      ∀ i : Fin n, R i (f (p i)) (f (q i)) (f i.succ) := by
  have hsep : ∀ i : Fin n, ∀ u ∈ ({p i, q i} : Finset (Fin (n + 1))),
      u.val ≤ i.val := by
    intro i u hu
    rcases Finset.mem_insert.mp hu with h | h
    · subst h
      exact hp i
    · rw [Finset.mem_singleton] at h
      subst h
      exact hq i
  have hdep : SepSupported (fun i => ({p i, q i} : Finset (Fin (n + 1))))
      (fun i g => R i (g (p i)) (g (q i)) (g i.succ)) := by
    intro i g g' hs hsucc
    show R i (g (p i)) (g (q i)) (g i.succ) ↔
      R i (g' (p i)) (g' (q i)) (g' i.succ)
    rw [hs (p i) (Finset.mem_insert_self _ _),
      hs (q i) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)),
      hsucc]
  have hDC' : DirectionalConsistent D
      (fun i g => R i (g (p i)) (g (q i)) (g i.succ)) := by
    intro i g hg
    obtain ⟨c, hc, hRc⟩ := hDC i g hg
    have hpne : p i ≠ i.succ := by
      intro h
      have h1 := hp i
      rw [h, Fin.val_succ] at h1
      omega
    have hqne : q i ≠ i.succ := by
      intro h
      have h1 := hq i
      rw [h, Fin.val_succ] at h1
      omega
    refine ⟨c, hc, ?_⟩
    show R i (Function.update g i.succ c (p i))
      (Function.update g i.succ c (q i))
      (Function.update g i.succ c i.succ)
    rw [Function.update_of_ne hpne, Function.update_of_ne hqne,
      Function.update_self]
    exact hRc
  obtain ⟨f, hf⟩ := directionalConsistent_solvable hsep hdep hDC' hne
  exact ⟨f, hf.1, hf.2⟩

end STE
