/-
Block decomposition: confining the exponential to the coupling core.

`Ste.Sheaf` proved the tractability dichotomy — variable-separable
(rectangular) constraints give a linear-space feasible set, while a
single coupling constraint is provably non-rectangular.  This file starts
the *decomposition* program: when the constraint hypergraph splits into
non-coupled blocks, the feasible set is a **product** over blocks, so the
exponential representation cost is confined to each block separately
rather than the whole variable set.  This is the abstract content of
variable elimination / treewidth: pay `∏` only inside a coupled block,
`∑` across independent blocks.

Model: the hypothesis space splits as `X × Y` (two blocks).  Block-1
constraints depend only on `X`, block-2 only on `Y`.  Then the feasible
set factors as `feas(C) ×ˢ feas(D)` (`feasibilitySet_blockFamily`) and
its cardinality multiplies (`encard_feasibilitySet_blockFamily`).

Reference: Combettes 1993; and the CSP tractability tradition (Freuder,
"A sufficient condition for backtrack-free search," JACM 1982; Dechter,
constraint decomposition / bucket elimination).
-/
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Prod
import Ste.Basic

namespace STE

open Set

variable {X Y ι κ : Type*}

/-- The combined constraint family on `X × Y` built from block-1
constraints `C` (depending only on the `X` coordinate) and block-2
constraints `D` (depending only on the `Y` coordinate), indexed by the
disjoint union of the two blocks. -/
def blockFamily (C : ι → Set X) (D : κ → Set Y) : ι ⊕ κ → Set (X × Y)
  | Sum.inl i => Prod.fst ⁻¹' C i
  | Sum.inr j => Prod.snd ⁻¹' D j

/-- **Block decomposition.**  With no constraint coupling the two blocks,
the feasible set factors as the product of the per-block feasible sets. -/
theorem feasibilitySet_blockFamily (C : ι → Set X) (D : κ → Set Y) :
    feasibilitySet (blockFamily C D)
      = feasibilitySet C ×ˢ feasibilitySet D := by
  ext ⟨x, y⟩
  simp only [feasibilitySet, blockFamily, Set.mem_iInter, Sum.forall,
    Set.mem_preimage, Set.mem_prod]

/-- **Multiplicative representation cost.**  Independent blocks multiply:
the feasible cardinality is the product of the per-block feasible
cardinalities.  Iterated, the exponential lives only inside each coupled
block — the `∑`-across-blocks, `∏`-within-block law. -/
theorem encard_feasibilitySet_blockFamily (C : ι → Set X) (D : κ → Set Y) :
    (feasibilitySet (blockFamily C D)).encard
      = (feasibilitySet C).encard * (feasibilitySet D).encard := by
  rw [feasibilitySet_blockFamily, Set.encard_prod]

end STE
