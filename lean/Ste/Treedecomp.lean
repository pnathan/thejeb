/-
Induced treewidth: the attained minimum elimination width.

`Ste.Elimination` proves that a complete elimination order of width `w`
decides a bucket list `B` in `n * k^(w+1)` total table space — with the
width `w` a FREE hypothesis on the given order.  This file discharges
that hypothesis:

* `AchievesWidth B w`: some complete elimination order materializes
  only bags of at most `w + 1` variables on `B`.
* `achievesWidth_card`: the trivial all-variables order `elimAll`
  witnesses `AchievesWidth B (Fintype.card V)` — the predicate is
  satisfiable, so the minimum below is over a nonempty set.
* `inducedTreewidth B`: the *induced treewidth* of the instance, the
  least achievable width, and `achievesWidth_inducedTreewidth`: the
  minimum is ATTAINED by a concrete optimal order.
* `bucketEliminate_treewidth_bound`: the unconditional bound — some
  complete order decides `B` in total table space
  `n * k^(inducedTreewidth B + 1)`.  No free width hypothesis remains.

What this file does NOT do: relate elimination width to graph-theoretic
tree decompositions (the equivalence with Robertson–Seymour treewidth),
or compute `inducedTreewidth` efficiently (that problem is NP-hard).
Both are outlook.

Reference: R. Dechter, *Constraint Processing*, 2003 (induced width);
N. Robertson, P. D. Seymour, treewidth.
-/
import Ste.Elimination
import Mathlib.Order.Lattice.Nat

namespace STE

open Set

variable {V : Type*} {A : V → Type*} [DecidableEq V]

/-! ### Achievable elimination width -/

/-- **Achievable width.**  The instance `B` *achieves width `w`* if some
elimination order is complete for `B` (its eliminated variables cover
every scope) and materializes only bags of at most `w + 1` variables
when run on `B`.  This is Dechter's induced width of the ordering,
quantified existentially over orderings. -/
def AchievesWidth (B : List (Finset V × Set (∀ v, A v))) (w : ℕ) : Prop :=
  ∃ order : List ((v : V) × A v),
    (∀ q ∈ B, (↑q.1 : Set V) ⊆ eliminated order)
      ∧ ∀ q ∈ bucketBags order B, q.1.card ≤ w + 1

/-- The trivial complete order: eliminate every variable once, with an
arbitrary value.  Its existence needs a finite variable set and
inhabited alphabets. -/
noncomputable def elimAll (V : Type*) (A : V → Type*) [Fintype V]
    [∀ v, Nonempty (A v)] : List ((v : V) × A v) :=
  Finset.univ.toList.map fun v => ⟨v, Classical.arbitrary (A v)⟩

/-- The trivial order eliminates every variable. -/
theorem eliminated_elimAll [Fintype V] [∀ v, Nonempty (A v)] :
    eliminated (elimAll V A) = Set.univ := by
  ext u
  simp only [Set.mem_univ, iff_true, eliminated, Set.mem_setOf_eq,
    elimAll, List.map_map]
  exact List.mem_map.mpr ⟨u, Finset.mem_toList.mpr (Finset.mem_univ u), rfl⟩

/-- **The width predicate is satisfiable.**  The trivial all-variables
order is complete for any instance, and every bag it materializes is a
`Finset` of variables, hence has at most `Fintype.card V` elements:
every instance achieves width `Fintype.card V`.  (Bags are sets of
variables, so nothing sharper than the number of variables is needed
for mere satisfiability.) -/
theorem achievesWidth_card [Fintype V] [∀ v, Nonempty (A v)]
    (B : List (Finset V × Set (∀ v, A v))) :
    AchievesWidth B (Fintype.card V) := by
  refine ⟨elimAll V A, ?_, ?_⟩
  · intro q _
    rw [eliminated_elimAll]
    exact Set.subset_univ _
  · intro q _
    exact le_trans (Finset.card_le_univ q.1) (Nat.le_succ _)

/-! ### Induced treewidth: the attained minimum -/

/-- **Induced treewidth** of the instance `B`: the least width any
complete elimination order achieves on `B`.  Well-defined as a natural
number because `achievesWidth_card` makes the set nonempty (over a
finite variable set with inhabited alphabets), and *attained*
(`achievesWidth_inducedTreewidth`): some concrete optimal order
realizes it. -/
noncomputable def inducedTreewidth
    (B : List (Finset V × Set (∀ v, A v))) : ℕ :=
  sInf {w | AchievesWidth B w}

/-- **The minimum width is attained.**  Some complete elimination order
achieves the induced treewidth of the instance: the infimum defining
`inducedTreewidth` is a minimum, realized by a concrete optimal
order. -/
theorem achievesWidth_inducedTreewidth [Fintype V] [∀ v, Nonempty (A v)]
    (B : List (Finset V × Set (∀ v, A v))) :
    AchievesWidth B (inducedTreewidth B) := by
  have h : sInf {w | AchievesWidth B w} ∈ {w | AchievesWidth B w} :=
    Nat.sInf_mem ⟨Fintype.card V, achievesWidth_card B⟩
  exact h

/-- The induced treewidth is a lower bound on every achievable width. -/
theorem inducedTreewidth_le {B : List (Finset V × Set (∀ v, A v))}
    {w : ℕ} (h : AchievesWidth B w) : inducedTreewidth B ≤ w := by
  have hw : w ∈ {w' | AchievesWidth B w'} := h
  exact Nat.sInf_le hw

/-- The induced treewidth never exceeds the number of variables. -/
theorem inducedTreewidth_le_card [Fintype V] [∀ v, Nonempty (A v)]
    (B : List (Finset V × Set (∀ v, A v))) :
    inducedTreewidth B ≤ Fintype.card V :=
  inducedTreewidth_le (achievesWidth_card B)

/-! ### The unconditional bound: the width hypothesis discharged -/

/-- **Bucket elimination at the attained induced treewidth.**  For any
instance `B` of scoped constraints (each supported on its scope) over a
finite variable set with inhabited alphabets of size at most `k`, there
EXISTS a complete elimination order that (i) covers every scope,
(ii) decides the substituted joint constraint — the elimination residue
is `univ` or `∅` — and (iii) materializes at most
`n * k^(inducedTreewidth B + 1)` total table rows, where `n` is the
length of the order.  The width hypothesis of
`bucketEliminate_total_space` is discharged: the bound holds at the
instance's own attained induced treewidth, with no free width
parameter. -/
theorem bucketEliminate_treewidth_bound [Fintype V]
    [∀ v, Nonempty (A v)] [∀ u, Fintype (A u)]
    (B : List (Finset V × Set (∀ v, A v))) {k : ℕ} (hk : 0 < k)
    (halpha : ∀ u : V, Fintype.card (A u) ≤ k)
    (hsupp : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V)) :
    ∃ order : List ((v : V) × A v),
      (∀ q ∈ B, (↑q.1 : Set V) ⊆ eliminated order)
        ∧ (eliminate order (joinConstraint B) = Set.univ
            ∨ eliminate order (joinConstraint B) = ∅)
        ∧ ((bucketBags order B).map
              fun q => (table (↑q.1 : Set V) q.2).encard).sum
            ≤ (order.length : ℕ∞)
                * ((k ^ (inducedTreewidth B + 1) : ℕ) : ℕ∞) := by
  obtain ⟨order, hcover, hwidth⟩ := achievesWidth_inducedTreewidth B
  exact ⟨order, hcover, (bucketEliminate_decides order hsupp hcover).2,
    bucketEliminate_total_space order B hk halpha hwidth⟩

end STE
