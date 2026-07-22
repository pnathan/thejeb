/-
n-ary block factorization: the "∏ within, ∑ across" law, quantitatively.

`Ste.Decomposition` proved the binary case: two non-coupled blocks give a
feasible set that is a product (`feasibilitySet_blockFamily`) whose
cardinality multiplies (`encard_feasibilitySet_blockFamily`).  This file
generalizes to an arbitrary finite family of independent blocks over a
dependent product space `∀ i, X i`: block `i`'s constraint depends only
on coordinate `i` (formally, it is the pullback of a set `C i ⊆ X i`
along the `i`-th projection, so it has support `{i}`).

Main results:

* `feasibilitySet_pullbackFamily`: the combined feasible set is exactly
  the box `Set.pi Set.univ C` — the n-ary product of the per-block
  feasible sets.
* `encard_feasibilitySet_blocks`: **the quantitative law** — the
  feasible cardinality is the finite product `∏ i, (C i).encard` of the
  per-block cardinalities.
* `encard_feasibilitySet_blockFamilies`: two-level version — when each
  block carries its own family of local constraints, the global feasible
  cardinality is the product of the per-block *feasibility-set*
  cardinalities: the exponential is paid inside each block separately.
* `encard_feasibilitySet_blocks_le`: the cost never exceeds the product
  of the block domain sizes.
* `encard_condition_univ_pi`, `encard_condition_univ_pi_mul`: the
  conditioned version for a single eliminated variable — after fixing
  `v := a` in a rectangular constraint, the residual feasible set still
  factors, with the `v`-th factor collapsing to the full (unconstrained)
  domain.

Reference: P. L. Combettes, "The Foundations of Set Theoretic
Estimation," Proc. IEEE 81(2), 1993 (feasibility as intersection);
R. Dechter, *Constraint Processing*, Morgan Kaufmann, 2003 (constraint
scopes, decomposition, and the `∑`-across-components /
`∏`-within-component complexity of tree-structured problems).
-/
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Ste.Basic
import Ste.Conditioning

namespace STE

open Set

variable {ι : Type*} {X : ι → Type*}

/-- The n-ary block constraint family on the dependent product
`∀ i, X i`: block `i` contributes the single constraint pulled back from
`C i ⊆ X i` along the `i`-th coordinate projection.  This is the n-ary
analogue of `blockFamily`: no constraint couples two distinct
coordinates. -/
def pullbackFamily (C : ∀ i, Set (X i)) : ι → Set (∀ i, X i) :=
  fun i => (fun f => f i) ⁻¹' C i

theorem mem_pullbackFamily_iff {C : ∀ i, Set (X i)} {i : ι}
    {f : ∀ i, X i} :
    f ∈ pullbackFamily C i ↔ f i ∈ C i :=
  Iff.rfl

/-- Each block constraint has singleton support: the constraint
hypergraph of `pullbackFamily C` consists of loops `{i}`, so distinct
blocks are non-coupled in the sense of `Ste.Support`. -/
theorem hasSupport_pullbackFamily (C : ∀ i, Set (X i)) (i : ι) :
    HasSupport (pullbackFamily C i) ({i} : Set ι) := by
  intro f g hfg
  simp only [pullbackFamily, Set.mem_preimage, hfg i rfl]

/-- Feasibility for the block family is coordinatewise feasibility. -/
theorem mem_feasibilitySet_pullbackFamily {C : ∀ i, Set (X i)}
    {f : ∀ i, X i} :
    f ∈ feasibilitySet (pullbackFamily C) ↔ ∀ i, f i ∈ C i := by
  simp only [mem_feasibilitySet, pullbackFamily, Set.mem_preimage]

/-- **n-ary block decomposition.**  With every constraint confined to a
single coordinate, the feasible set is exactly the box
`Set.pi Set.univ C` — the n-ary product of the per-block feasible sets.
This generalizes the binary `feasibilitySet_blockFamily` of
`Ste.Decomposition`. -/
theorem feasibilitySet_pullbackFamily (C : ∀ i, Set (X i)) :
    feasibilitySet (pullbackFamily C) = Set.pi Set.univ C := by
  ext f
  rw [mem_feasibilitySet_pullbackFamily, Set.mem_univ_pi]

/-- **The quantitative factorization law** (`∏` within blocks, `∑`
across).  For finitely many independent blocks the feasible cardinality
is the *finite product* of the per-block feasible cardinalities.  The
multiplicative — exponential in the number of blocks — representation
cost is thereby confined to each block separately: an estimator may pay
`∑ i, cost(C i)` across blocks instead of `∏ i, cost(C i)` for the
joint set, which is the abstract content of variable elimination on a
disconnected constraint hypergraph (Combettes 1993, §II-C, feasibility
as intersection; Dechter 2003, decomposition into independent
components). -/
theorem encard_feasibilitySet_blocks [Fintype ι] (C : ∀ i, Set (X i)) :
    (feasibilitySet (pullbackFamily C)).encard = ∏ i, (C i).encard := by
  rw [feasibilitySet_pullbackFamily]
  exact Set.encard_pi_eq_prod_encard

/-- **Two-level factorization**: when block `i` carries its own family
of local constraints `S i`, the global feasible set of all pulled-back
local constraints has cardinality `∏ i, (feasibilitySet (S i)).encard`.
Whatever exponential blowup the local families induce stays inside
their own block. -/
theorem encard_feasibilitySet_blockFamilies [Fintype ι] {κ : ι → Type*}
    (S : ∀ i, κ i → Set (X i)) :
    (feasibilitySet (pullbackFamily fun i => feasibilitySet (S i))).encard
      = ∏ i, (feasibilitySet (S i)).encard :=
  encard_feasibilitySet_blocks _

/-- **Cost upper bound.**  A decoupled problem never costs more than the
product of its block domain sizes; any small block caps the total
accordingly. -/
theorem encard_feasibilitySet_blocks_le [Fintype ι] (C : ∀ i, Set (X i)) :
    (feasibilitySet (pullbackFamily C)).encard
      ≤ ∏ i, (Set.univ : Set (X i)).encard := by
  rw [← Set.encard_pi_eq_prod_encard, feasibilitySet_pullbackFamily]
  exact Set.encard_mono (Set.pi_mono fun i _ => Set.subset_univ _)

/-! ### The conditioned version: elimination preserves factorization

After fixing (conditioning on) a variable `v := a`, a rectangular
constraint stays rectangular (`condition_pi`, from `Ste.Conditioning`),
so the residual feasible set still factors as a finite product — with
the eliminated coordinate contributing the full-domain factor, since it
is no longer constrained. -/

variable {V : Type*} {A : V → Type*} [DecidableEq V] [Fintype V]

/-- **Conditioned factorization.**  Fixing `v := a` (with `a` feasible
for block `v`) in the box `Set.univ.pi P` leaves a residual feasible
set that again factors as a finite product: the `v`-th factor is
replaced by the full domain and every other factor is untouched. -/
theorem encard_condition_univ_pi (P : ∀ v, Set (A v)) {v : V} {a : A v}
    (ha : a ∈ P v) :
    (condition (Set.univ.pi P) v a).encard
      = ∏ w, (Function.update P v Set.univ w).encard := by
  rw [condition_pi P ha]
  exact Set.encard_pi_eq_prod_encard

/-- **Conditioned factorization, explicit form**: the residual cost after
eliminating `v` is the domain size at `v` times the product of the
remaining block cardinalities — eliminating a variable removes exactly
its factor from the constrained product (Dechter 2003, bucket
elimination). -/
theorem encard_condition_univ_pi_mul (P : ∀ v, Set (A v)) {v : V}
    {a : A v} (ha : a ∈ P v) :
    (condition (Set.univ.pi P) v a).encard
      = (Set.univ : Set (A v)).encard
          * ∏ w ∈ Finset.univ \ {v}, (P w).encard := by
  rw [encard_condition_univ_pi P ha]
  calc
    ∏ w, (Function.update P v Set.univ w).encard
        = ∏ w, Function.update (fun u => (P u).encard) v
            (Set.univ : Set (A v)).encard w :=
      Finset.prod_congr rfl fun w _ =>
        Function.apply_update (fun u (s : Set (A u)) => s.encard) P v
          Set.univ w
    _ = _ := Finset.prod_update_of_mem (Finset.mem_univ v) _ _

end STE
