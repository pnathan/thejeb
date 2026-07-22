/-
The converse bound: from a tree decomposition back to an elimination
order.

`Ste.GraphTreewidth` proves the forward bound
`treewidth (primalGraph B) ≤ inducedTreewidth B + 1` by running an
optimal bucket-elimination order and assembling its trace into a tree
decomposition.  This file proves the CONVERSE: every tree decomposition
of the primal graph can be turned back into a complete elimination
order whose every message scope fits inside a bag minus its eliminated
variable.  Together the two bounds give the exact equality between
Robertson–Seymour treewidth and Dechter's bucket-elimination induced
width (offset by the eliminated variable each elimination bag carries).

The classical route (Bodlaender 1998, *A partial k-arboretum of graphs
with bounded treewidth*) repeatedly eliminates a simplicial vertex
found in a leaf bag.  We formalize an equivalent but induction-friendlier
scheme adapted to the rooted parent-function presentation of
`TreeDecomposition`:

* `TreeDecomposition.top`: the *topmost* position (largest list index)
  of a bag containing a given vertex — well defined by `vertexCover`.
* `TreeDecomposition.mem_top_of_shared_bag` (the **chain lemma**, the
  combinatorial heart): if `u` and `x` share a bag and
  `top u ≤ top x`, then `x` already lies in the topmost bag of `u`.
  Proof: walk the parent chain from the shared bag; running
  intersection keeps both `u` and `x` in every bag along the chain,
  and the strictly increasing chain hits `top u` exactly.
* `bucketBags_card_le_of_pairwise_top`: eliminating the variables in
  ascending order of `top` keeps every live scope pairwise-covered by
  bags, so each message scope lands inside `bags[top u] \ {u}` — card
  at most (bag size) − 1.  This replaces the simplicial-vertex/leaf-bag
  induction and never needs the Helly clique-in-a-bag lemma: the
  invariant is kept *pairwise* (any two variables of a live scope share
  a bag), which `edgeCover` provides outright for the initial scopes.
* `achievesWidth_of_treeDecomposition`: the extraction — a tree
  decomposition of `primalGraph B` with bags of size at most `k + 1`
  yields a complete order for `B` whose message scopes have at most
  `k` variables.
* `inducedTreewidth_le_treewidth_sub_one`: the unconditional converse
  bound `inducedTreewidth B ≤ treewidth (primalGraph B) - 1` (natural
  subtraction).
* `inducedTreewidth_add_one_le_treewidth` and the equality
  `treewidth_primalGraph_eq`: when the primal graph has at least one
  edge, `treewidth (primalGraph B) = inducedTreewidth B + 1`.
* `max_treewidth_primalGraph_one_eq`: the fully unconditional form,
  `max (treewidth (primalGraph B)) 1 = inducedTreewidth B + 1`.

The edge hypothesis on the equality is SHARP, not an artifact: for an
edgeless primal graph (e.g. `B = []` or all scopes singletons) the
singleton-bag decomposition gives `treewidth = 0` while
`inducedTreewidth B + 1 = 1`; both `treewidth` and `inducedTreewidth`
truncate at zero and the one-variable offset has nowhere to go.  The
`max · 1` equality absorbs exactly this degeneracy and holds with no
hypotheses at all.

References: H. L. Bodlaender, *A partial k-arboretum of graphs with
bounded treewidth*, Theor. Comput. Sci. 209 (1998) (elimination orders
vs. tree decompositions); R. Dechter, *Constraint Processing*, 2003
(induced width); N. Robertson, P. D. Seymour, *Graph minors II*
(treewidth).
-/
import Ste.GraphTreewidth
import Mathlib.Data.List.Sort

namespace STE

open Set

variable {V : Type*} {A : V → Type*} [DecidableEq V]

/-! ### List and foldr helpers -/

private theorem getD_mem_of_lt {α : Type*} :
    ∀ {l : List α} {i : ℕ} {d : α}, i < l.length → l.getD i d ∈ l
  | _ :: _, 0, _, _ => List.mem_cons_self
  | a :: _, _ + 1, _, h =>
      List.mem_cons_of_mem a (getD_mem_of_lt (Nat.lt_of_succ_lt_succ h))

private theorem exists_getD_eq_of_mem {α : Type*} {l : List α} {b : α}
    (d : α) (h : b ∈ l) : ∃ i, i < l.length ∧ l.getD i d = b := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
      rcases List.mem_cons.mp h with rfl | h
      · refine ⟨0, ?_, List.getD_cons_zero⟩
        rw [List.length_cons]
        omega
      · obtain ⟨i, hi, hgd⟩ := ih h
        refine ⟨i + 1, ?_, ?_⟩
        · rw [List.length_cons]
          omega
        · rw [List.getD_cons_succ]
          exact hgd

private theorem le_foldr_max {l : List ℕ} {x : ℕ} (h : x ∈ l) :
    x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)

/-! ### The topmost bag of a vertex -/

/-- **The topmost bag position of a vertex**: the largest list index of
a bag containing `u`.  Well defined (`top_spec`) because `vertexCover`
makes the set of such positions nonempty and it is bounded by the
number of bags. -/
noncomputable def TreeDecomposition.top {G : SimpleGraph V}
    (td : TreeDecomposition G) (u : V) : ℕ :=
  sSup {i | i < td.bags.length ∧ u ∈ td.bags.getD i ∅}

/-- The topmost position is a genuine position and its bag contains the
vertex. -/
theorem TreeDecomposition.top_spec {G : SimpleGraph V}
    (td : TreeDecomposition G) (u : V) :
    td.top u < td.bags.length ∧ u ∈ td.bags.getD (td.top u) ∅ := by
  have hne : {i | i < td.bags.length ∧ u ∈ td.bags.getD i ∅}.Nonempty := by
    obtain ⟨b, hb, hub⟩ := td.vertexCover u
    obtain ⟨i, hi, hgd⟩ := exists_getD_eq_of_mem ∅ hb
    exact ⟨i, hi, hgd ▸ hub⟩
  have hbdd : BddAbove {i | i < td.bags.length ∧ u ∈ td.bags.getD i ∅} :=
    ⟨td.bags.length, fun i hi => le_of_lt hi.1⟩
  exact Nat.sSup_mem hne hbdd

/-- Every position whose bag contains `u` is at most `top u`. -/
theorem TreeDecomposition.le_top {G : SimpleGraph V}
    (td : TreeDecomposition G) {u : V} {i : ℕ}
    (hi : i < td.bags.length) (hu : u ∈ td.bags.getD i ∅) :
    i ≤ td.top u :=
  le_csSup ⟨td.bags.length, fun j hj => le_of_lt hj.1⟩ ⟨hi, hu⟩

/-- **The chain lemma** — the combinatorial heart of the converse
bound.  If `u` and `x` share the bag at position `i` and
`top u ≤ top x`, then `x` lies in the topmost bag of `u`.

Walk the parent chain from `i`: by running intersection (parent-closure
form) both `u` and `x` stay in every bag along the chain as long as the
position is below their respective tops, the chain is strictly
increasing, and it cannot overshoot `top u` — a chain bag containing
`u` is at position at most `top u` by maximality.  So the chain lands
on `top u` exactly, carrying `x` with it.  (This is the rooted-tree
avatar of the classical fact that the bags containing a vertex form a
connected subtree, applied to the subtree of `u` and the deeper subtree
of `x`.) -/
theorem TreeDecomposition.mem_top_of_shared_bag {G : SimpleGraph V}
    (td : TreeDecomposition G) {u x : V} {i : ℕ}
    (hi : i < td.bags.length)
    (hu : u ∈ td.bags.getD i ∅) (hx : x ∈ td.bags.getD i ∅)
    (hle : td.top u ≤ td.top x) :
    x ∈ td.bags.getD (td.top u) ∅ := by
  have key : ∀ n : ℕ, ∀ j : ℕ, j < td.bags.length →
      u ∈ td.bags.getD j ∅ → x ∈ td.bags.getD j ∅ →
      td.top u - j ≤ n → x ∈ td.bags.getD (td.top u) ∅ := by
    intro n
    induction n with
    | zero =>
        intro j hj hju hjx hn
        have h1 : j ≤ td.top u := td.le_top hj hju
        have h2 : j = td.top u := by omega
        rwa [h2] at hjx
    | succ n ihn =>
        intro j hj hju hjx hn
        have h1 : j ≤ td.top u := td.le_top hj hju
        rcases eq_or_lt_of_le h1 with heq | hlt
        · rwa [heq] at hjx
        · have htu1 : td.top u < td.bags.length := (td.top_spec u).1
          have htu2 : u ∈ td.bags.getD (td.top u) ∅ := (td.top_spec u).2
          have htx1 : td.top x < td.bags.length := (td.top_spec x).1
          have htx2 : x ∈ td.bags.getD (td.top x) ∅ := (td.top_spec x).2
          have hjlen : j + 1 < td.bags.length := by omega
          have hju' : u ∈ td.bags.getD (td.parent j) ∅ :=
            td.runningIntersection u j (td.top u) hlt htu1 hju htu2
          have hjx' : x ∈ td.bags.getD (td.parent j) ∅ :=
            td.runningIntersection x j (td.top x)
              (lt_of_lt_of_le hlt hle) htx1 hjx htx2
          have hpgt : j < td.parent j := td.parent_gt j hjlen
          have hplt : td.parent j < td.bags.length := td.parent_lt j hjlen
          have hple : td.parent j ≤ td.top u := td.le_top hplt hju'
          exact ihn (td.parent j) hplt hju' hjx' (by omega)
  exact key (td.top u) i hi hu hx (by omega)

/-! ### Bounded buckets along a top-sorted order -/

/-- **Eliminating in ascending `top` order keeps every message scope
inside a bag minus its eliminated variable.**  The induction carries
two invariants on the live state `S`: every variable of every live
scope is still to be eliminated (`hlive`), and any two variables of a
live scope share a bag (`hpair` — the pairwise weakening of "every
live scope fits in a bag", which sidesteps the Helly clique-in-a-bag
lemma).  At the step eliminating `u = p.1`, any other variable `x` of
the merged scope shares a bag with `u` and is eliminated later, so
`top u ≤ top x` and the chain lemma puts `x` in `bags[top u]`; hence
the message scope is inside `bags[top u] \ {u}`, of size at most `k`,
and both invariants pass to the next state. -/
theorem bucketBags_card_le_of_pairwise_top {G : SimpleGraph V}
    (td : TreeDecomposition G) {k : ℕ}
    (hbag : ∀ b ∈ td.bags, b.card ≤ k + 1) :
    ∀ (order : List ((v : V) × A v))
      (S : List (Finset V × Set (∀ v, A v))),
      List.Pairwise (fun p s => td.top p.1 ≤ td.top s.1) order →
      (∀ q ∈ S, ∀ x ∈ q.1, x ∈ order.map Sigma.fst) →
      (∀ q ∈ S, ∀ x ∈ q.1, ∀ y ∈ q.1,
        ∃ i, i < td.bags.length
          ∧ x ∈ td.bags.getD i ∅ ∧ y ∈ td.bags.getD i ∅) →
      ∀ q ∈ bucketBags order S, q.1.card ≤ k := by
  intro order
  induction order with
  | nil =>
      intro S _ _ _ q hq
      simp at hq
  | cons p order ih =>
      intro S hsort hlive hpair q hq
      rw [bucketBags_cons] at hq
      -- the key subset claim: the message scope of this step is inside
      -- the topmost bag of the eliminated variable, minus that variable
      have hsub : (bucketHead p S).1
          ⊆ (td.bags.getD (td.top p.1) ∅).erase p.1 := by
        intro x hx
        rw [bucketHead_fst] at hx
        have hxne : x ≠ p.1 := (Finset.mem_erase.mp hx).1
        obtain ⟨qq, hqq, hxqq⟩ :=
          mem_joinScope.mp (Finset.mem_of_mem_erase hx)
        have hqqS : qq ∈ S := List.mem_of_mem_filter hqq
        have hpqq : p.1 ∈ qq.1 :=
          of_decide_eq_true (List.mem_filter.mp hqq).2
        obtain ⟨i, hilen, hxi, hpi⟩ := hpair qq hqqS x hxqq p.1 hpqq
        have hxorder : x ∈ order.map Sigma.fst := by
          have h1 := hlive qq hqqS x hxqq
          rw [List.map_cons] at h1
          rcases List.mem_cons.mp h1 with h | h
          · exact absurd h hxne
          · exact h
        obtain ⟨s, hs, hsx⟩ := List.mem_map.mp hxorder
        have htople : td.top p.1 ≤ td.top x := by
          have h2 := (List.pairwise_cons.mp hsort).1 s hs
          rw [hsx] at h2
          exact h2
        exact Finset.mem_erase.mpr
          ⟨hxne, td.mem_top_of_shared_bag hilen hpi hxi htople⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · -- the bag materialized at this step
        have hmem : p.1 ∈ td.bags.getD (td.top p.1) ∅ := (td.top_spec p.1).2
        have hcard1 : ((td.bags.getD (td.top p.1) ∅).erase p.1).card
            = (td.bags.getD (td.top p.1) ∅).card - 1 :=
          Finset.card_erase_of_mem hmem
        have hcard2 : (td.bags.getD (td.top p.1) ∅).card ≤ k + 1 :=
          hbag _ (getD_mem_of_lt (td.top_spec p.1).1)
        have hcard3 := Finset.card_le_card hsub
        omega
      · -- the remaining steps: both invariants pass to the next state
        refine ih (bucketStep p S) (List.pairwise_cons.mp hsort).2
          ?_ ?_ q hq
        · -- liveness invariant
          intro qq hqq x hx
          rw [bucketStep_eq] at hqq
          rcases List.mem_cons.mp hqq with rfl | hqq
          · rw [bucketHead_fst] at hx
            have hxne : x ≠ p.1 := (Finset.mem_erase.mp hx).1
            obtain ⟨rr, hrr, hxrr⟩ :=
              mem_joinScope.mp (Finset.mem_of_mem_erase hx)
            have h1 := hlive rr (List.mem_of_mem_filter hrr) x hxrr
            rw [List.map_cons] at h1
            rcases List.mem_cons.mp h1 with h | h
            · exact absurd h hxne
            · exact h
          · have hqqS : qq ∈ S := List.mem_of_mem_filter hqq
            have hpn : p.1 ∉ qq.1 :=
              of_decide_eq_true (List.mem_filter.mp hqq).2
            have h1 := hlive qq hqqS x hx
            rw [List.map_cons] at h1
            rcases List.mem_cons.mp h1 with h | h
            · exact absurd (h ▸ hx) hpn
            · exact h
        · -- pairwise bag-sharing invariant
          intro qq hqq x hx y hy
          rw [bucketStep_eq] at hqq
          rcases List.mem_cons.mp hqq with rfl | hqq
          · exact ⟨td.top p.1, (td.top_spec p.1).1,
              Finset.mem_of_mem_erase (hsub hx),
              Finset.mem_of_mem_erase (hsub hy)⟩
          · exact hpair qq (List.mem_of_mem_filter hqq) x hx y hy

/-! ### The extraction: from a tree decomposition to an order -/

/-- **The converse extraction.**  From a tree decomposition of the
primal graph with bags of at most `k + 1` variables, produce a complete
elimination order for `B` whose every message scope has at most `k`
variables: eliminate all variables in ascending order of their topmost
bag position.  The initial pairwise invariant is exactly `edgeCover`
(two distinct co-occurring variables are primal-adjacent) plus
`vertexCover` (for the degenerate pair `x = x`). -/
theorem achievesWidth_of_treeDecomposition [Fintype V]
    [∀ v, Nonempty (A v)] (B : List (Finset V × Set (∀ v, A v)))
    (td : TreeDecomposition (primalGraph B)) {k : ℕ}
    (hbag : ∀ b ∈ td.bags, b.card ≤ k + 1) :
    ∃ order : List ((v : V) × A v),
      (∀ q ∈ B, (↑q.1 : Set V) ⊆ eliminated order)
        ∧ ∀ q ∈ bucketBags order B, q.1.card ≤ k := by
  classical
  set r : ((v : V) × A v) → ((v : V) × A v) → Prop :=
    fun p s => td.top p.1 ≤ td.top s.1 with hr
  haveI : DecidableRel r := fun p s => Nat.decLe _ _
  haveI : IsTrans ((v : V) × A v) r :=
    ⟨fun _ _ _ hab hbc => le_trans hab hbc⟩
  haveI : Std.Total r := ⟨fun _ _ => le_total _ _⟩
  set order := List.insertionSort r (elimAll V A) with horder
  have hmem : ∀ x : V, x ∈ order.map Sigma.fst := by
    intro x
    refine List.mem_map.mpr ⟨⟨x, Classical.arbitrary (A x)⟩, ?_, rfl⟩
    rw [horder, List.mem_insertionSort]
    simp only [elimAll]
    exact List.mem_map.mpr
      ⟨x, Finset.mem_toList.mpr (Finset.mem_univ x), rfl⟩
  refine ⟨order, ?_, ?_⟩
  · intro q hq x hx
    exact mem_eliminated.mpr (hmem x)
  · refine bucketBags_card_le_of_pairwise_top td hbag order B ?_ ?_ ?_
    · exact List.pairwise_insertionSort r (elimAll V A)
    · intro q hq x hx
      exact hmem x
    · intro q hq x hx y hy
      by_cases hxy : x = y
      · subst hxy
        obtain ⟨b, hb, hxb⟩ := td.vertexCover x
        obtain ⟨i, hi, hgd⟩ := exists_getD_eq_of_mem ∅ hb
        exact ⟨i, hi, hgd ▸ hxb, hgd ▸ hxb⟩
      · obtain ⟨b, hb, hxb, hyb⟩ :=
          td.edgeCover (show (primalGraph B).Adj x y from
            ⟨hxy, q, hq, hx, hy⟩)
        obtain ⟨i, hi, hgd⟩ := exists_getD_eq_of_mem ∅ hb
        exact ⟨i, hi, hgd ▸ hxb, hgd ▸ hyb⟩

/-! ### The converse bound and the equality -/

/-- **The unconditional converse bound.**  The induced treewidth is at
most the treewidth of the primal graph minus one (natural
subtraction): take an optimal tree decomposition — its bags have at
most `treewidth + 1` variables — and extract an order whose message
scopes have at most `treewidth` variables. -/
theorem inducedTreewidth_le_treewidth_sub_one [Fintype V]
    [∀ v, Nonempty (A v)] (B : List (Finset V × Set (∀ v, A v))) :
    inducedTreewidth B ≤ treewidth (primalGraph B) - 1 := by
  obtain ⟨td, htd⟩ :=
    exists_treeDecomposition_width_le_treewidth (primalGraph B)
  have hbag : ∀ b ∈ td.bags, b.card ≤ treewidth (primalGraph B) + 1 := by
    intro b hb
    have h1 : b.card ≤ (td.bags.map Finset.card).foldr max 0 :=
      le_foldr_max (List.mem_map.mpr ⟨b, hb, rfl⟩)
    have h2 : (td.bags.map Finset.card).foldr max 0 - 1
        ≤ treewidth (primalGraph B) := htd
    omega
  obtain ⟨order, hcov, hwidth⟩ :=
    achievesWidth_of_treeDecomposition B td hbag
  refine inducedTreewidth_le ⟨order, hcov, fun q hq => ?_⟩
  have h3 := hwidth q hq
  omega

/-- A graph with an edge has treewidth at least one: any tree
decomposition has a bag containing both endpoints. -/
theorem one_le_treewidth_of_adj [Fintype V] {G : SimpleGraph V}
    {u v : V} (h : G.Adj u v) : 1 ≤ treewidth G := by
  obtain ⟨td, htd⟩ := exists_treeDecomposition_width_le_treewidth G
  obtain ⟨b, hb, hub, hvb⟩ := td.edgeCover h
  have h1 : 1 < b.card := Finset.one_lt_card.mpr ⟨u, hub, v, hvb, h.ne⟩
  have h2 : b.card ≤ (td.bags.map Finset.card).foldr max 0 :=
    le_foldr_max (List.mem_map.mpr ⟨b, hb, rfl⟩)
  have h3 : (td.bags.map Finset.card).foldr max 0 - 1 ≤ treewidth G := htd
  omega

/-- **The converse bound, headline form.**  Whenever the primal graph
is not edgeless (equivalently, its treewidth is positive — some scope
has two variables), the induced treewidth plus one is at most the
treewidth of the primal graph. -/
theorem inducedTreewidth_add_one_le_treewidth [Fintype V]
    [∀ v, Nonempty (A v)] (B : List (Finset V × Set (∀ v, A v)))
    (h : 1 ≤ treewidth (primalGraph B)) :
    inducedTreewidth B + 1 ≤ treewidth (primalGraph B) := by
  have h1 := inducedTreewidth_le_treewidth_sub_one B
  omega

/-- **The equality.**  For any instance whose primal graph has at least
one edge, Robertson–Seymour treewidth and bucket-elimination induced
width coincide, offset by the eliminated variable each elimination bag
carries: `treewidth (primalGraph B) = inducedTreewidth B + 1`.  The
edge hypothesis is sharp — see the module docstring. -/
theorem treewidth_primalGraph_eq [Fintype V] [∀ v, Nonempty (A v)]
    (B : List (Finset V × Set (∀ v, A v))) {u v : V}
    (h : (primalGraph B).Adj u v) :
    treewidth (primalGraph B) = inducedTreewidth B + 1 :=
  le_antisymm (treewidth_primalGraph_le B)
    (inducedTreewidth_add_one_le_treewidth B (one_le_treewidth_of_adj h))

/-- **The unconditional equality.**  With the degenerate edgeless case
absorbed into a `max`, the equivalence of treewidth and induced width
holds with no hypotheses:
`max (treewidth (primalGraph B)) 1 = inducedTreewidth B + 1`. -/
theorem max_treewidth_primalGraph_one_eq [Fintype V]
    [∀ v, Nonempty (A v)] (B : List (Finset V × Set (∀ v, A v))) :
    max (treewidth (primalGraph B)) 1 = inducedTreewidth B + 1 := by
  have h1 := treewidth_primalGraph_le B
  have h2 := inducedTreewidth_le_treewidth_sub_one B
  omega

end STE
