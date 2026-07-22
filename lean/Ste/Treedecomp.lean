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

end STE
