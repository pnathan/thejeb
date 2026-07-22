/-
Graph treewidth and the elimination tree decomposition.

`Ste.Treedecomp` defines the induced treewidth of a bucket-list instance
`B` — the least width any complete elimination order achieves on `B`.
This file builds the graph-theoretic side of the bridge, from scratch
(Mathlib has `SimpleGraph` but no tree decompositions):

* `primalGraph B`: the primal (co-occurrence) graph of the instance —
  two distinct variables are adjacent iff some scope contains both.
  Every scope is a clique (`isClique_scope`).
* `TreeDecomposition G`: a Robertson–Seymour tree decomposition,
  presented as a list of bags together with a *parent function* on
  positions: `parent i > i`, so positions form a tree rooted at the
  last bag.  Running intersection is stated as parent-closure: if a
  vertex appears in bag `i` and in some later bag, it appears in bag
  `parent i`.  For an increasing parent function this is equivalent to
  the usual "the bags containing each vertex form a connected subtree":
  walking parents from any bag containing `u` strictly increases the
  position, stays among bags containing `u`, and terminates at the
  topmost such bag, which is therefore a common ancestor realizing
  connectedness; conversely a connected family is parent-closed below
  its topmost element.  Rooted presentations of this kind are standard
  (Bodlaender's "nice" tree decompositions).
* `TreeDecomposition.width` and `treewidth G`: max bag size minus one,
  and the least width of any tree decomposition — well-defined and
  attained because the single-bag decomposition `TreeDecomposition.single`
  always exists over a `Fintype`.
* `elimBags order B`: the bags of the *elimination tree decomposition*:
  at each step the recorded message scope (`bucketHead`) plus the
  eliminated variable itself.  `elimBags_edge_cover`,
  `elimBags_mem_of_eliminated`, `elimBags_card_le`: edge coverage,
  vertex coverage, and the width accounting — each elimination bag has
  at most `w + 2` variables when the order achieves width `w`.
* `primalGraph_elimination_cover`: the assembled unconditional
  statement — some list of bags covers every vertex and every primal
  edge of `B`, all bags of size at most `inducedTreewidth B + 2`.
* `InertLe`, `exists_nodup_order`: empty-scope constraints are inert
  for bucket elimination, so duplicated elimination steps can be
  dropped — every order dedupes with a sublist of its bags.
* `exists_elim_treeDecomposition`: the recursive construction of the
  full elimination tree decomposition, including the
  running-intersection axiom, for duplicate-free complete orders.
* `treewidth_primalGraph_le`: the headline bound
  `treewidth (primalGraph B) ≤ inducedTreewidth B + 1` — graph
  treewidth and bucket-elimination induced width measure the same
  quantity, offset by the eliminated variable each bag carries.

References: R. Dechter, *Constraint Processing*, 2003 (induced width,
bucket elimination); N. Robertson, P. D. Seymour, *Graph minors II*
(tree decompositions, treewidth); H. L. Bodlaender, *A partial
k-arboretum of graphs with bounded treewidth* (elimination orders and
treewidth).
-/
import Ste.Treedecomp
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace STE

open Set

variable {V : Type*} {A : V → Type*} [DecidableEq V]

/-! ### The primal graph of an instance -/

/-- **The primal graph** (co-occurrence graph) of a bucket-list
instance: two distinct variables are adjacent iff some scope of `B`
contains both. -/
def primalGraph (B : List (Finset V × Set (∀ v, A v))) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ q ∈ B, u ∈ q.1 ∧ v ∈ q.1
  symm := by
    constructor
    intro u v h
    obtain ⟨huv, q, hq, hu, hv⟩ := h
    exact ⟨huv.symm, q, hq, hv, hu⟩
  loopless := by
    constructor
    intro u h
    exact h.1 rfl

theorem primalGraph_adj {B : List (Finset V × Set (∀ v, A v))} {u v : V} :
    (primalGraph B).Adj u v ↔ u ≠ v ∧ ∃ q ∈ B, u ∈ q.1 ∧ v ∈ q.1 :=
  Iff.rfl

/-- **Every scope is a clique** of the primal graph. -/
theorem isClique_scope {B : List (Finset V × Set (∀ v, A v))}
    {q : Finset V × Set (∀ v, A v)} (hq : q ∈ B) :
    (primalGraph B).IsClique (↑q.1 : Set V) := by
  rw [SimpleGraph.isClique_iff]
  intro u hu v hv huv
  exact ⟨huv, q, hq, Finset.mem_coe.mp hu, Finset.mem_coe.mp hv⟩

/-! ### Tree decompositions -/

/-- **A tree decomposition** of `G`, presented as a list of bags with a
parent function on positions.  `parent i > i` for every non-final
position, so the positions form a tree rooted at the last bag.  The
three Robertson–Seymour axioms: every vertex is in some bag
(`vertexCover`); every edge is inside some bag (`edgeCover`); and
running intersection in parent-closure form (`runningIntersection`):
a vertex lying in bag `i` and in any later bag lies in bag `parent i`.
For an increasing parent function this is equivalent to the usual
requirement that the bags containing a fixed vertex form a connected
subtree (see the module docstring). -/
structure TreeDecomposition (G : SimpleGraph V) where
  /-- The bags, indexed by list position. -/
  bags : List (Finset V)
  /-- The tree structure: each position's parent. -/
  parent : ℕ → ℕ
  /-- Parents strictly increase (the tree is rooted at the last bag). -/
  parent_gt : ∀ i, i + 1 < bags.length → i < parent i
  /-- Parents stay in range. -/
  parent_lt : ∀ i, i + 1 < bags.length → parent i < bags.length
  /-- Every vertex occurs in some bag. -/
  vertexCover : ∀ v : V, ∃ b ∈ bags, v ∈ b
  /-- Both endpoints of every edge occur in a common bag. -/
  edgeCover : ∀ ⦃u v : V⦄, G.Adj u v → ∃ b ∈ bags, u ∈ b ∧ v ∈ b
  /-- Running intersection, parent-closure form: a vertex in bag `i`
  and in some later bag is in bag `parent i`. -/
  runningIntersection : ∀ u : V, ∀ i j : ℕ, i < j → j < bags.length →
    u ∈ bags.getD i ∅ → u ∈ bags.getD j ∅ → u ∈ bags.getD (parent i) ∅

/-- The width of a tree decomposition: the largest bag size minus one. -/
def TreeDecomposition.width {G : SimpleGraph V}
    (td : TreeDecomposition G) : ℕ :=
  (td.bags.map Finset.card).foldr max 0 - 1

private theorem foldr_max_le {l : List ℕ} {c : ℕ} (h : ∀ x ∈ l, x ≤ c) :
    l.foldr max 0 ≤ c := by
  induction l with
  | nil => exact Nat.zero_le c
  | cons a l ih =>
      exact max_le (h a List.mem_cons_self)
        (ih fun x hx => h x (List.mem_cons_of_mem a hx))

/-- Width from a uniform bag-size bound. -/
theorem TreeDecomposition.width_le {G : SimpleGraph V}
    (td : TreeDecomposition G) {w : ℕ}
    (h : ∀ b ∈ td.bags, b.card ≤ w + 1) : td.width ≤ w := by
  have hm : (td.bags.map Finset.card).foldr max 0 ≤ w + 1 :=
    foldr_max_le fun x hx => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      exact h b hb
  show (td.bags.map Finset.card).foldr max 0 - 1 ≤ w
  omega

/-- The one-bag tree decomposition: every vertex in a single bag.  It
witnesses that every finite graph has a tree decomposition. -/
def TreeDecomposition.single [Fintype V] (G : SimpleGraph V) :
    TreeDecomposition G where
  bags := [Finset.univ]
  parent := id
  parent_gt := by
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    omega
  parent_lt := by
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    omega
  vertexCover := fun v => ⟨Finset.univ, List.mem_cons_self, Finset.mem_univ v⟩
  edgeCover := fun u v _ =>
    ⟨Finset.univ, List.mem_cons_self, Finset.mem_univ u, Finset.mem_univ v⟩
  runningIntersection := by
    intro u i j hij hj _ _
    simp only [List.length_cons, List.length_nil] at hj
    omega

/-- **Treewidth** of a finite graph: the least width over all tree
decompositions.  The set is nonempty (`TreeDecomposition.single`), so
the infimum is attained (`exists_treeDecomposition_width_le_treewidth`). -/
noncomputable def treewidth [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf {w | ∃ td : TreeDecomposition G, td.width ≤ w}

/-- Every tree decomposition bounds the treewidth. -/
theorem treewidth_le_width [Fintype V] {G : SimpleGraph V}
    (td : TreeDecomposition G) : treewidth G ≤ td.width :=
  Nat.sInf_le ⟨td, le_rfl⟩

/-- **The treewidth is attained**: some tree decomposition has width at
most `treewidth G`. -/
theorem exists_treeDecomposition_width_le_treewidth [Fintype V]
    (G : SimpleGraph V) : ∃ td : TreeDecomposition G, td.width ≤ treewidth G := by
  have h : sInf {w | ∃ td : TreeDecomposition G, td.width ≤ w}
      ∈ {w | ∃ td : TreeDecomposition G, td.width ≤ w} :=
    Nat.sInf_mem ⟨(TreeDecomposition.single G).width,
      ⟨TreeDecomposition.single G, le_rfl⟩⟩
  exact h

/-- The treewidth of a graph on `n` vertices is at most `n - 1`. -/
theorem treewidth_le_card [Fintype V] (G : SimpleGraph V) :
    treewidth G ≤ Fintype.card V - 1 :=
  (treewidth_le_width (TreeDecomposition.single G)).trans
    ((TreeDecomposition.single G).width_le fun b hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · rw [Finset.card_univ]
        omega
      · simp at hb)

/-! ### The elimination bags -/

/-- Membership in `eliminated` is list membership of the variable. -/
theorem mem_eliminated {order : List ((v : V) × A v)} {u : V} :
    u ∈ eliminated order ↔ u ∈ order.map Sigma.fst :=
  Iff.rfl

theorem eliminated_append (o₁ o₂ : List ((v : V) × A v)) :
    eliminated (o₁ ++ o₂) = eliminated o₁ ∪ eliminated o₂ := by
  ext u
  simp [eliminated, Set.mem_setOf_eq, List.mem_append]

/-- **The elimination bags**: at each elimination step, the recorded
message scope (`bucketHead`) together with the eliminated variable
itself.  These are the bags of the elimination tree decomposition —
each is one variable larger than the message scope recorded in
`bucketBags`. -/
def elimBags : List ((v : V) × A v) → List (Finset V × Set (∀ v, A v))
    → List (Finset V)
  | [], _ => []
  | p :: order, B =>
      insert p.1 (bucketHead p B).1 :: elimBags order (bucketStep p B)

@[simp] theorem elimBags_nil (B : List (Finset V × Set (∀ v, A v))) :
    elimBags [] B = [] := rfl

theorem elimBags_cons (p : (v : V) × A v) (order : List ((v : V) × A v))
    (B : List (Finset V × Set (∀ v, A v))) :
    elimBags (p :: order) B
      = insert p.1 (bucketHead p B).1 :: elimBags order (bucketStep p B) :=
  rfl

theorem elimBags_append (o₁ o₂ : List ((v : V) × A v))
    (B : List (Finset V × Set (∀ v, A v))) :
    elimBags (o₁ ++ o₂) B
      = elimBags o₁ B ++ elimBags o₂ (bucketEliminate o₁ B) := by
  induction o₁ generalizing B with
  | nil => rfl
  | cons p o₁ ih =>
      rw [List.cons_append, elimBags_cons, elimBags_cons, ih,
        bucketEliminate_cons, List.cons_append]

/-- **Width accounting.**  If every message scope the order records has
at most `w + 1` variables, every elimination bag has at most `w + 2`:
the bag is the message scope plus the eliminated variable. -/
theorem elimBags_card_le {order : List ((v : V) × A v)}
    {B : List (Finset V × Set (∀ v, A v))} {w : ℕ}
    (h : ∀ q ∈ bucketBags order B, q.1.card ≤ w + 1) :
    ∀ b ∈ elimBags order B, b.card ≤ w + 2 := by
  induction order generalizing B with
  | nil =>
      intro b hb
      simp at hb
  | cons p order ih =>
      intro b hb
      rw [elimBags_cons] at hb
      rcases List.mem_cons.mp hb with rfl | hb
      · have h1 : (bucketHead p B).1.card ≤ w + 1 := by
          refine h (bucketHead p B) ?_
          rw [bucketBags_cons]
          exact List.mem_cons_self
        have h2 := Finset.card_insert_le p.1 (bucketHead p B).1
        omega
      · refine ih (fun q hq => ?_) b hb
        refine h q ?_
        rw [bucketBags_cons]
        exact List.mem_cons_of_mem _ hq

/-- **Vertex coverage.**  Every eliminated variable occurs in the
elimination bag of its own step. -/
theorem elimBags_mem_of_eliminated (order : List ((v : V) × A v))
    (B : List (Finset V × Set (∀ v, A v))) {v : V}
    (hv : v ∈ eliminated order) :
    ∃ b ∈ elimBags order B, v ∈ b := by
  induction order generalizing B with
  | nil =>
      rw [eliminated_nil] at hv
      exact absurd hv (Set.notMem_empty v)
  | cons p order ih =>
      rcases List.mem_cons.mp (mem_eliminated.mp hv) with h1 | h1
      · refine ⟨insert p.1 (bucketHead p B).1, List.mem_cons_self, ?_⟩
        rw [h1]
        exact Finset.mem_insert_self p.1 (bucketHead p B).1
      · obtain ⟨b, hb, hvb⟩ := ih (bucketStep p B) (mem_eliminated.mpr h1)
        exact ⟨b, List.mem_cons_of_mem _ hb, hvb⟩

private theorem mem_insert_erase {s : Finset V} {a u : V} (hu : u ∈ s) :
    u ∈ insert a (s.erase a) := by
  by_cases h : u = a
  · rw [h]
    exact Finset.mem_insert_self a _
  · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h, hu⟩)

/-- **Coverage passes to the next state.**  After the step at `p`, the
live scopes are covered by the remaining order. -/
theorem bucketStep_cov (p : (v : V) × A v) {order : List ((v : V) × A v)}
    {B : List (Finset V × Set (∀ v, A v))}
    (hcov : ∀ q ∈ B, (↑q.1 : Set V) ⊆ eliminated (p :: order)) :
    ∀ q ∈ bucketStep p B, (↑q.1 : Set V) ⊆ eliminated order := by
  intro r hr x hx
  obtain ⟨hxe, hxne⟩ := bucketStep_scope_subset p hcov r hr hx
  rcases List.mem_cons.mp (mem_eliminated.mp hxe) with h1 | h1
  · exact absurd (Set.mem_singleton_iff.mpr h1) hxne
  · exact mem_eliminated.mpr h1

/-- **Edge coverage.**  For a complete order, every primal edge of the
instance lands inside some elimination bag: an edge `{u, v}` witnessed
by a scope survives (possibly merged into message constraints) until
the first step eliminating a variable of that scope, whose bag then
contains the whole current scope — in particular `u` and `v`. -/
theorem elimBags_edge_cover {order : List ((v : V) × A v)}
    {B : List (Finset V × Set (∀ v, A v))}
    (hcov : ∀ q ∈ B, (↑q.1 : Set V) ⊆ eliminated order)
    {u v : V} (h : (primalGraph B).Adj u v) :
    ∃ b ∈ elimBags order B, u ∈ b ∧ v ∈ b := by
  induction order generalizing B with
  | nil =>
      obtain ⟨huv, q, hq, hu, hv⟩ := h
      have h1 := hcov q hq (Finset.mem_coe.mpr hu)
      rw [eliminated_nil] at h1
      exact absurd h1 (Set.notMem_empty u)
  | cons p order ih =>
      obtain ⟨huv, q, hq, hu, hv⟩ := h
      by_cases hp : p.1 ∈ q.1
      · -- the scope of `q` is merged into this step's bag
        have hqf : q ∈ B.filter fun r => p.1 ∈ r.1 :=
          List.mem_filter.mpr ⟨hq, decide_eq_true hp⟩
        refine ⟨insert p.1 (bucketHead p B).1, List.mem_cons_self, ?_, ?_⟩
        · exact mem_insert_erase (mem_joinScope.mpr ⟨q, hqf, hu⟩)
        · exact mem_insert_erase (mem_joinScope.mpr ⟨q, hqf, hv⟩)
      · -- the scope of `q` survives untouched into the next state
        have hcov' : ∀ r ∈ bucketStep p B,
            (↑r.1 : Set V) ⊆ eliminated order := bucketStep_cov p hcov
        have hq' : q ∈ bucketStep p B :=
          List.mem_cons_of_mem _
            (List.mem_filter.mpr ⟨hq, decide_eq_true hp⟩)
        obtain ⟨b, hb, hub, hvb⟩ := ih hcov' ⟨huv, q, hq', hu, hv⟩
        exact ⟨b, List.mem_cons_of_mem _ hb, hub, hvb⟩

/-! ### Padding a complete order to cover every vertex -/

/-- If every scope in the state is empty, so is every join scope. -/
theorem joinScope_eq_empty {L : List (Finset V × Set (∀ v, A v))}
    (h : ∀ q ∈ L, q.1 = ∅) : joinScope L = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr fun u hu => ?_
  obtain ⟨q, hq, hqu⟩ := mem_joinScope.mp hu
  rw [h q hq] at hqu
  exact Finset.notMem_empty u hqu

theorem bucketHead_fst_eq_empty {p : (v : V) × A v}
    {B : List (Finset V × Set (∀ v, A v))} (h : ∀ q ∈ B, q.1 = ∅) :
    (bucketHead p B).1 = ∅ := by
  rw [bucketHead_fst,
    joinScope_eq_empty fun q hq => h q (List.mem_of_mem_filter hq),
    Finset.erase_empty]

theorem bucketStep_scopes_empty (p : (v : V) × A v)
    {B : List (Finset V × Set (∀ v, A v))} (h : ∀ q ∈ B, q.1 = ∅) :
    ∀ q ∈ bucketStep p B, q.1 = ∅ := by
  intro q hq
  rw [bucketStep_eq] at hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact bucketHead_fst_eq_empty h
  · exact h q (List.mem_of_mem_filter hq)

/-- Eliminating variables in a fully decided state materializes only
singleton bags. -/
theorem elimBags_card_le_one {order : List ((v : V) × A v)}
    {B : List (Finset V × Set (∀ v, A v))} (h : ∀ q ∈ B, q.1 = ∅) :
    ∀ b ∈ elimBags order B, b.card ≤ 1 := by
  induction order generalizing B with
  | nil =>
      intro b hb
      simp at hb
  | cons p order ih =>
      intro b hb
      rw [elimBags_cons] at hb
      rcases List.mem_cons.mp hb with rfl | hb
      · rw [bucketHead_fst_eq_empty h]
        simp
      · exact ih (bucketStep_scopes_empty p h) b hb

/-- After a complete order, every live scope is empty. -/
theorem bucketEliminate_scopes_empty {order : List ((v : V) × A v)}
    {B : List (Finset V × Set (∀ v, A v))}
    (hcov : ∀ q ∈ B, (↑q.1 : Set V) ⊆ eliminated order) :
    ∀ q ∈ bucketEliminate order B, q.1 = ∅ := by
  intro q hq
  have h := bucketEliminate_scope_subset order hcov q hq
  rwa [Set.sdiff_self, Set.subset_empty_iff, Finset.coe_eq_empty] at h

/-- Pad an order with the not-yet-eliminated variables (with arbitrary
values), so that the padded order eliminates every variable. -/
noncomputable def padOrder [Fintype V] [∀ v, Nonempty (A v)]
    (order : List ((v : V) × A v)) : List ((v : V) × A v) :=
  (Finset.univ.toList.filter fun v => v ∉ order.map Sigma.fst).map
    fun v => ⟨v, Classical.arbitrary (A v)⟩

theorem padOrder_map_fst [Fintype V] [∀ v, Nonempty (A v)]
    (order : List ((v : V) × A v)) :
    (padOrder order).map Sigma.fst
      = Finset.univ.toList.filter fun v => v ∉ order.map Sigma.fst := by
  simp [padOrder, List.map_map, Function.comp_def]

/-- The padded order eliminates every variable. -/
theorem eliminated_append_padOrder [Fintype V] [∀ v, Nonempty (A v)]
    (order : List ((v : V) × A v)) :
    eliminated (order ++ padOrder order) = Set.univ := by
  refine Set.eq_univ_of_forall fun u => ?_
  rw [eliminated_append]
  by_cases h : u ∈ order.map Sigma.fst
  · exact Set.mem_union_left _ (mem_eliminated.mpr h)
  · refine Set.mem_union_right _ (mem_eliminated.mpr ?_)
    rw [padOrder_map_fst]
    exact List.mem_filter.mpr
      ⟨Finset.mem_toList.mpr (Finset.mem_univ u), decide_eq_true h⟩

/-! ### The assembled coverage statement -/

/-- **The elimination construction covers the primal graph at the
induced treewidth.**  For any instance `B` there is a list of bags —
the elimination bags of an optimal order, padded to all variables —
such that every vertex is in some bag, both endpoints of every primal
edge share a bag, and every bag has at most `inducedTreewidth B + 2`
variables (message scope plus eliminated variable).  These are the
vertex-coverage, edge-coverage, and width axioms of the elimination
tree decomposition; the remaining running-intersection axiom is
developed separately. -/
theorem primalGraph_elimination_cover [Fintype V] [∀ v, Nonempty (A v)]
    (B : List (Finset V × Set (∀ v, A v))) :
    ∃ bags : List (Finset V),
      (∀ v : V, ∃ b ∈ bags, v ∈ b)
        ∧ (∀ ⦃u v : V⦄, (primalGraph B).Adj u v → ∃ b ∈ bags, u ∈ b ∧ v ∈ b)
        ∧ ∀ b ∈ bags, b.card ≤ inducedTreewidth B + 2 := by
  obtain ⟨order, hcov, hwidth⟩ := achievesWidth_inducedTreewidth B
  refine ⟨elimBags (order ++ padOrder order) B, ?_, ?_, ?_⟩
  · intro v
    refine elimBags_mem_of_eliminated _ B ?_
    rw [eliminated_append_padOrder]
    trivial
  · intro u v huv
    refine elimBags_edge_cover ?_ huv
    intro q hq
    rw [eliminated_append]
    exact (hcov q hq).trans Set.subset_union_left
  · intro b hb
    rw [elimBags_append] at hb
    rcases List.mem_append.mp hb with hb | hb
    · exact elimBags_card_le hwidth b hb
    · have h1 := elimBags_card_le_one
        (bucketEliminate_scopes_empty hcov) b hb
      omega

/-! ### Inert constraints and duplicate-free orders

An empty-scope constraint never joins any bucket: it is *inert* for
bucket elimination.  `InertLe B B'` says `B'` is `B` with inert
constraints interleaved; such states materialize the same bags.  A
step whose variable no live scope contains only produces an inert
residue, so it can be dropped without changing the remaining bags —
in particular any *duplicated* elimination step.  Hence every instance
runs on a duplicate-free order with a sublist of the original bags
(`exists_nodup_order`). -/

/-- `InertLe B B'`: `B'` is `B` with extra empty-scope (inert)
constraints interleaved. -/
inductive InertLe : List (Finset V × Set (∀ v, A v)) →
    List (Finset V × Set (∀ v, A v)) → Prop
  | nil : InertLe [] []
  | cons (q) {B B'} : InertLe B B' → InertLe (q :: B) (q :: B')
  | inert (T) {B B'} : InertLe B B' → InertLe B ((∅, T) :: B')

theorem InertLe.refl (B : List (Finset V × Set (∀ v, A v))) :
    InertLe B B := by
  induction B with
  | nil => exact .nil
  | cons q B ih => exact .cons q ih

/-- Inert constraints never enter a bucket. -/
theorem InertLe.filter_mem {B B' : List (Finset V × Set (∀ v, A v))}
    (h : InertLe B B') (v : V) :
    (B.filter fun q => v ∈ q.1) = B'.filter fun q => v ∈ q.1 := by
  induction h with
  | nil => rfl
  | cons q h ih =>
      by_cases hv : v ∈ q.1
      · rw [List.filter_cons_of_pos (by simpa using hv),
          List.filter_cons_of_pos (by simpa using hv), ih]
      · rw [List.filter_cons_of_neg (by simpa using hv),
          List.filter_cons_of_neg (by simpa using hv), ih]
  | inert T h ih =>
      rw [List.filter_cons_of_neg (by simp), ih]

/-- Inert constraints survive the complement filter, inertly. -/
theorem InertLe.filter_not_mem {B B' : List (Finset V × Set (∀ v, A v))}
    (h : InertLe B B') (v : V) :
    InertLe (B.filter fun q => v ∉ q.1) (B'.filter fun q => v ∉ q.1) := by
  induction h with
  | nil => exact .nil
  | cons q h ih =>
      by_cases hv : v ∈ q.1
      · rw [List.filter_cons_of_neg (by simp [hv]),
          List.filter_cons_of_neg (by simp [hv])]
        exact ih
      · rw [List.filter_cons_of_pos (by simpa using hv),
          List.filter_cons_of_pos (by simpa using hv)]
        exact .cons q ih
  | inert T h ih =>
      rw [List.filter_cons_of_pos (by simp)]
      exact .inert T ih

theorem InertLe.bucketHead_eq {B B' : List (Finset V × Set (∀ v, A v))}
    (h : InertLe B B') (p : (v : V) × A v) :
    bucketHead p B = bucketHead p B' := by
  show ((joinScope (B.filter fun q => p.1 ∈ q.1)).erase p.1,
      condition (joinConstraint (B.filter fun q => p.1 ∈ q.1)) p.1 p.2)
    = ((joinScope (B'.filter fun q => p.1 ∈ q.1)).erase p.1,
      condition (joinConstraint (B'.filter fun q => p.1 ∈ q.1)) p.1 p.2)
  rw [h.filter_mem p.1]

theorem InertLe.bucketStep_le {B B' : List (Finset V × Set (∀ v, A v))}
    (h : InertLe B B') (p : (v : V) × A v) :
    InertLe (bucketStep p B) (bucketStep p B') := by
  rw [bucketStep_eq, bucketStep_eq, h.bucketHead_eq p]
  exact .cons _ (h.filter_not_mem p.1)

/-- **Inert constraints do not change the recorded bags.** -/
theorem InertLe.bucketBags_eq {B B' : List (Finset V × Set (∀ v, A v))}
    (h : InertLe B B') (order : List ((v : V) × A v)) :
    bucketBags order B = bucketBags order B' := by
  induction order generalizing B B' with
  | nil => rfl
  | cons p order ih =>
      rw [bucketBags_cons, bucketBags_cons, h.bucketHead_eq p,
        ih (h.bucketStep_le p)]

/-- A step at a variable no live scope contains only adds an inert
residue. -/
theorem inertLe_bucketStep_self {p : (v : V) × A v}
    {B : List (Finset V × Set (∀ v, A v))} (h : ∀ q ∈ B, p.1 ∉ q.1) :
    InertLe B (bucketStep p B) := by
  have hfilter : (B.filter fun q => p.1 ∉ q.1) = B :=
    List.filter_eq_self.mpr fun q hq => decide_eq_true (h q hq)
  have hbag : (bucketHead p B).1 = ∅ := by
    have hf : (B.filter fun q => p.1 ∈ q.1) = [] :=
      List.filter_eq_nil_iff.mpr fun q hq hmem =>
        h q hq (of_decide_eq_true hmem)
    rw [bucketHead_fst, hf, joinScope_nil, Finset.erase_empty]
  have hpair : bucketHead p B = (∅, (bucketHead p B).2) := by
    rw [← hbag]
  rw [bucketStep_eq, hfilter, hpair]
  exact .inert _ (InertLe.refl B)

/-- Such a step leaves all later bags unchanged. -/
theorem bucketBags_cons_of_forall_not_mem {p : (v : V) × A v}
    {B : List (Finset V × Set (∀ v, A v))} (h : ∀ q ∈ B, p.1 ∉ q.1)
    (order : List ((v : V) × A v)) :
    bucketBags (p :: order) B = bucketHead p B :: bucketBags order B := by
  rw [bucketBags_cons]
  congr 1
  exact ((inertLe_bucketStep_self h).bucketBags_eq order).symm

/-- After the step at `p`, no live scope contains `p.1`. -/
theorem bucketStep_not_mem_scope (p : (v : V) × A v)
    (B : List (Finset V × Set (∀ v, A v))) :
    ∀ q ∈ bucketStep p B, p.1 ∉ q.1 := by
  intro q hq
  rw [bucketStep_eq] at hq
  rcases List.mem_cons.mp hq with rfl | hq
  · rw [bucketHead_fst]
    exact Finset.notMem_erase p.1 _
  · exact of_decide_eq_true (List.mem_filter.mp hq).2

/-- A variable absent from all live scopes stays absent. -/
theorem bucketStep_not_mem_scope_of (p : (v : V) × A v)
    {B : List (Finset V × Set (∀ v, A v))} {x : V}
    (h : ∀ q ∈ B, x ∉ q.1) : ∀ q ∈ bucketStep p B, x ∉ q.1 := by
  intro q hq
  rw [bucketStep_eq] at hq
  rcases List.mem_cons.mp hq with rfl | hq
  · rw [bucketHead_fst]
    intro hx
    obtain ⟨q', hq', hxq'⟩ := mem_joinScope.mp (Finset.mem_of_mem_erase hx)
    exact h q' (List.mem_of_mem_filter hq') hxq'
  · exact h q (List.mem_of_mem_filter hq)

/-- **Dropping a redundant step.**  A step whose variable was already
eliminated earlier (or never occurs in any live scope) can be removed:
the remaining bags form a sublist of the original ones. -/
theorem bucketBags_removal (p : (v : V) × A v)
    (pre : List ((v : V) × A v)) :
    ∀ (post : List ((v : V) × A v))
      (B : List (Finset V × Set (∀ v, A v))),
      (p.1 ∈ pre.map Sigma.fst ∨ ∀ q ∈ B, p.1 ∉ q.1) →
      (bucketBags (pre ++ post) B).Sublist
        (bucketBags (pre ++ p :: post) B) := by
  induction pre with
  | nil =>
      intro post B h
      rcases h with h | h
      · simp at h
      · rw [List.nil_append, List.nil_append,
          bucketBags_cons_of_forall_not_mem h post]
        exact List.sublist_cons_self _ _
  | cons r pre ih =>
      intro post B h
      rw [List.cons_append, List.cons_append, bucketBags_cons,
        bucketBags_cons]
      refine List.Sublist.cons_cons _ (ih post (bucketStep r B) ?_)
      rcases h with h | h
      · rw [List.map_cons] at h
        rcases List.mem_cons.mp h with h1 | h1
        · refine Or.inr ?_
          rw [h1]
          exact bucketStep_not_mem_scope r B
        · exact Or.inl h1
      · exact Or.inr (bucketStep_not_mem_scope_of r h)

/-- A repetition in an order splits it around a step whose variable
already occurred. -/
theorem exists_dup_decomposition {order : List ((v : V) × A v)}
    (h : ¬ (order.map Sigma.fst).Nodup) :
    ∃ (pre : List ((v : V) × A v)) (p : (v : V) × A v)
      (post : List ((v : V) × A v)),
      order = pre ++ p :: post ∧ p.1 ∈ pre.map Sigma.fst := by
  induction order with
  | nil => exact absurd List.nodup_nil h
  | cons r order ih =>
      by_cases h1 : (order.map Sigma.fst).Nodup
      · have hr : r.1 ∈ order.map Sigma.fst := by
          by_contra hr
          rw [List.map_cons, List.nodup_cons] at h
          exact h ⟨hr, h1⟩
        obtain ⟨p, hp, hpfst⟩ := List.mem_map.mp hr
        obtain ⟨s, t, rfl⟩ := List.append_of_mem hp
        refine ⟨r :: s, p, t, rfl, ?_⟩
        rw [List.map_cons]
        exact List.mem_cons.mpr (Or.inl hpfst)
      · obtain ⟨pre, p, post, rfl, hp⟩ := ih h1
        refine ⟨r :: pre, p, post, rfl, ?_⟩
        rw [List.map_cons]
        exact List.mem_cons_of_mem _ hp

/-- Removing a duplicated step does not change the eliminated set. -/
theorem eliminated_middle {pre post : List ((v : V) × A v)}
    {p : (v : V) × A v} (hp : p.1 ∈ pre.map Sigma.fst) :
    eliminated (pre ++ post) = eliminated (pre ++ p :: post) := by
  ext u
  simp only [mem_eliminated, List.map_append, List.mem_append,
    List.map_cons, List.mem_cons]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl h
    · refine Or.inl ?_
      rw [h]
      exact hp
    · exact Or.inr h

/-- **Every order dedupes.**  Some duplicate-free order eliminates the
same variables and materializes, on every instance, a sublist of the
original bags. -/
theorem exists_nodup_order (order : List ((v : V) × A v)) :
    ∃ order' : List ((v : V) × A v),
      (order'.map Sigma.fst).Nodup
        ∧ eliminated order' = eliminated order
        ∧ ∀ B : List (Finset V × Set (∀ v, A v)),
            (bucketBags order' B).Sublist (bucketBags order B) := by
  generalize hn : order.length = n
  induction n using Nat.strong_induction_on generalizing order with
  | _ n ih =>
      by_cases hnd : (order.map Sigma.fst).Nodup
      · exact ⟨order, hnd, rfl, fun B => List.Sublist.refl _⟩
      · obtain ⟨pre, p, post, heq, hp⟩ := exists_dup_decomposition hnd
        subst heq
        obtain ⟨order', h1, h2, h3⟩ :=
          ih (pre ++ post).length
            (by rw [← hn]
                simp only [List.length_append, List.length_cons]
                omega)
            (pre ++ post) rfl
        refine ⟨order', h1, ?_, fun B => (h3 B).trans
          (bucketBags_removal p pre post B (Or.inl hp))⟩
        rw [h2]
        exact eliminated_middle hp

/-! ### Auxiliary facts about appended orders -/

theorem bucketBags_append (o₁ o₂ : List ((v : V) × A v))
    (B : List (Finset V × Set (∀ v, A v))) :
    bucketBags (o₁ ++ o₂) B
      = bucketBags o₁ B ++ bucketBags o₂ (bucketEliminate o₁ B) := by
  induction o₁ generalizing B with
  | nil => rfl
  | cons p o₁ ih =>
      rw [List.cons_append, bucketBags_cons, bucketBags_cons, ih,
        bucketEliminate_cons, List.cons_append]

/-- On a fully decided state, all recorded bags are empty. -/
theorem bucketBags_fst_empty {order : List ((v : V) × A v)}
    {B : List (Finset V × Set (∀ v, A v))} (h : ∀ q ∈ B, q.1 = ∅) :
    ∀ q ∈ bucketBags order B, q.1 = ∅ := by
  induction order generalizing B with
  | nil =>
      intro q hq
      simp at hq
  | cons p order ih =>
      intro q hq
      rw [bucketBags_cons] at hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact bucketHead_fst_eq_empty h
      · exact ih (bucketStep_scopes_empty p h) q hq

/-! ### The elimination tree decomposition -/

private theorem getD_mem_of_lt {α : Type*} :
    ∀ {l : List α} {i : ℕ} {d : α}, i < l.length → l.getD i d ∈ l
  | _ :: _, 0, _, _ => List.mem_cons_self
  | a :: _, _ + 1, _, h =>
      List.mem_cons_of_mem a (getD_mem_of_lt (Nat.lt_of_succ_lt_succ h))

/-- Extend a parent function under a new bag at position `0`: the new
bag's parent is `t + 1`; all other positions shift by one. -/
def consParent (t : ℕ) (parent : ℕ → ℕ) : ℕ → ℕ
  | 0 => t + 1
  | i + 1 => parent i + 1

@[simp] theorem consParent_zero (t : ℕ) (parent : ℕ → ℕ) :
    consParent t parent 0 = t + 1 := rfl

@[simp] theorem consParent_succ (t : ℕ) (parent : ℕ → ℕ) (i : ℕ) :
    consParent t parent (i + 1) = parent i + 1 := rfl

/-- **The elimination tree decomposition, recursively.**  Running a
duplicate-free complete elimination order on a state `B` yields bags
(one per elimination step — the message scope plus the eliminated
variable — plus a terminal empty bag) and a parent function (each step
points at the first later bag containing its message scope) satisfying
all three tree-decomposition axioms for the primal graph of `B`,
together with the bookkeeping invariants that drive the recursion:
scope coverage (every live scope is inside some bag), provenance (bags
contain only scope variables or order variables — this is what makes
running intersection close: the eliminated variable never reappears),
and width provenance (every bag is empty or a recorded message scope
plus one variable). -/
theorem exists_elim_treeDecomposition :
    ∀ (order : List ((v : V) × A v))
      (B : List (Finset V × Set (∀ v, A v))),
      (order.map Sigma.fst).Nodup →
      (∀ q ∈ B, (↑q.1 : Set V) ⊆ eliminated order) →
      ∃ (bags : List (Finset V)) (parent : ℕ → ℕ),
        bags.length = order.length + 1
          ∧ (∀ i, i + 1 < bags.length → i < parent i)
          ∧ (∀ i, i + 1 < bags.length → parent i < bags.length)
          ∧ (∀ q ∈ B, ∃ i, i < bags.length ∧ q.1 ⊆ bags.getD i ∅)
          ∧ (∀ u v : V, (primalGraph B).Adj u v →
              ∃ b ∈ bags, u ∈ b ∧ v ∈ b)
          ∧ (∀ x : V, x ∈ order.map Sigma.fst → ∃ b ∈ bags, x ∈ b)
          ∧ (∀ b ∈ bags, ∀ x ∈ b,
              (∃ q ∈ B, x ∈ q.1) ∨ x ∈ order.map Sigma.fst)
          ∧ (∀ u : V, ∀ i j : ℕ, i < j → j < bags.length →
              u ∈ bags.getD i ∅ → u ∈ bags.getD j ∅ →
              u ∈ bags.getD (parent i) ∅)
          ∧ (∀ b ∈ bags, b = ∅
              ∨ ∃ q ∈ bucketBags order B, ∃ x : V, b = insert x q.1) := by
  intro order
  induction order with
  | nil =>
      intro B _ hcov
      have hempty : ∀ q ∈ B, q.1 = ∅ := by
        intro q hq
        have h := hcov q hq
        rwa [eliminated_nil, Set.subset_empty_iff, Finset.coe_eq_empty]
          at h
      refine ⟨[∅], id, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i hi
        simp only [List.length_cons, List.length_nil] at hi
        omega
      · intro i hi
        simp only [List.length_cons, List.length_nil] at hi
        omega
      · intro q hq
        refine ⟨0, Nat.zero_lt_one, ?_⟩
        rw [hempty q hq]
        exact Finset.empty_subset _
      · intro u v huv
        obtain ⟨_, q, hq, hu, _⟩ := huv
        rw [hempty q hq] at hu
        exact absurd hu (Finset.notMem_empty u)
      · intro x hx
        simp at hx
      · intro b hb x hxb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact absurd hxb (Finset.notMem_empty x)
        · simp at hb
      · intro u i j hij hjlen _ _
        simp only [List.length_cons, List.length_nil] at hjlen
        omega
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact Or.inl rfl
        · simp at hb
  | cons p order ih =>
      intro B hnd hcov
      rw [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hpnotin, hnd'⟩ := hnd
      obtain ⟨bags', parent', hlen', hpg', hpl', hsc', hec', hvc',
        hprov', hri', hwb'⟩ :=
        ih (bucketStep p B) hnd' (bucketStep_cov p hcov)
      obtain ⟨j0, hj0len, hj0sub⟩ :=
        hsc' (bucketHead p B)
          (by rw [bucketStep_eq]; exact List.mem_cons_self)
      refine ⟨insert p.1 (bucketHead p B).1 :: bags',
        consParent j0 parent', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      -- length
      · simp only [List.length_cons, hlen']
      -- parents grow
      · intro i hi
        simp only [List.length_cons] at hi
        rcases i with _ | k
        · simp only [consParent_zero]
          omega
        · simp only [consParent_succ]
          have := hpg' k (by omega)
          omega
      -- parents stay in range
      · intro i hi
        simp only [List.length_cons] at hi ⊢
        rcases i with _ | k
        · simp only [consParent_zero]
          omega
        · simp only [consParent_succ]
          have := hpl' k (by omega)
          omega
      -- scope coverage
      · intro q hq
        by_cases hp : p.1 ∈ q.1
        · refine ⟨0, ?_, ?_⟩
          · simp only [List.length_cons]
            omega
          · rw [List.getD_cons_zero]
            intro x hx
            exact mem_insert_erase (mem_joinScope.mpr
              ⟨q, List.mem_filter.mpr ⟨hq, decide_eq_true hp⟩, hx⟩)
        · obtain ⟨i, hilen, hisub⟩ := hsc' q (List.mem_cons_of_mem _
            (List.mem_filter.mpr ⟨hq, decide_eq_true hp⟩))
          refine ⟨i + 1, ?_, ?_⟩
          · simp only [List.length_cons]
            omega
          · rw [List.getD_cons_succ]
            exact hisub
      -- edge coverage
      · intro u v huv
        obtain ⟨hune, q, hq, hu, hv⟩ := huv
        by_cases hp : p.1 ∈ q.1
        · have hqf : q ∈ B.filter fun r => p.1 ∈ r.1 :=
            List.mem_filter.mpr ⟨hq, decide_eq_true hp⟩
          exact ⟨insert p.1 (bucketHead p B).1, List.mem_cons_self,
            mem_insert_erase (mem_joinScope.mpr ⟨q, hqf, hu⟩),
            mem_insert_erase (mem_joinScope.mpr ⟨q, hqf, hv⟩)⟩
        · have hq' : q ∈ bucketStep p B := List.mem_cons_of_mem _
            (List.mem_filter.mpr ⟨hq, decide_eq_true hp⟩)
          obtain ⟨b, hb, hub, hvb⟩ := hec' u v ⟨hune, q, hq', hu, hv⟩
          exact ⟨b, List.mem_cons_of_mem _ hb, hub, hvb⟩
      -- vertex coverage of the eliminated variables
      · intro x hx
        rw [List.map_cons] at hx
        rcases List.mem_cons.mp hx with h1 | h1
        · refine ⟨insert p.1 (bucketHead p B).1, List.mem_cons_self, ?_⟩
          rw [h1]
          exact Finset.mem_insert_self p.1 _
        · obtain ⟨b, hb, hxb⟩ := hvc' x h1
          exact ⟨b, List.mem_cons_of_mem _ hb, hxb⟩
      -- provenance
      · intro b hb x hxb
        rcases List.mem_cons.mp hb with rfl | hb
        · rcases Finset.mem_insert.mp hxb with rfl | hx
          · refine Or.inr ?_
            rw [List.map_cons]
            exact List.mem_cons_self
          · rw [bucketHead_fst] at hx
            obtain ⟨r, hr, hxr⟩ :=
              mem_joinScope.mp (Finset.mem_of_mem_erase hx)
            exact Or.inl ⟨r, List.mem_of_mem_filter hr, hxr⟩
        · rcases hprov' b hb x hxb with ⟨q, hq, hxq⟩ | hx
          · rw [bucketStep_eq] at hq
            rcases List.mem_cons.mp hq with rfl | hq
            · rw [bucketHead_fst] at hxq
              obtain ⟨r, hr, hxr⟩ :=
                mem_joinScope.mp (Finset.mem_of_mem_erase hxq)
              exact Or.inl ⟨r, List.mem_of_mem_filter hr, hxr⟩
            · exact Or.inl ⟨q, List.mem_of_mem_filter hq, hxq⟩
          · refine Or.inr ?_
            rw [List.map_cons]
            exact List.mem_cons_of_mem _ hx
      -- running intersection
      · intro u i j hij hjlen hui huj
        simp only [List.length_cons] at hjlen
        rcases i with _ | k
        · rcases j with _ | m
          · omega
          · rw [List.getD_cons_zero] at hui
            rw [List.getD_cons_succ] at huj
            simp only [consParent_zero]
            rw [List.getD_cons_succ]
            have hm : m < bags'.length := by omega
            have hune : u ≠ p.1 := by
              intro heq
              rcases hprov' _ (getD_mem_of_lt hm) u huj with
                ⟨q, hq, hxq⟩ | hx
              · exact bucketStep_not_mem_scope p B q hq (heq ▸ hxq)
              · exact hpnotin (heq ▸ hx)
            have hu' : u ∈ (bucketHead p B).1 := by
              rcases Finset.mem_insert.mp hui with h | h
              · exact absurd h hune
              · exact h
            exact hj0sub hu'
        · rcases j with _ | m
          · omega
          · rw [List.getD_cons_succ] at hui huj
            simp only [consParent_succ]
            rw [List.getD_cons_succ]
            exact hri' u k m (by omega) (by omega) hui huj
      -- width provenance
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · refine Or.inr ⟨bucketHead p B, ?_, p.1, rfl⟩
          rw [bucketBags_cons]
          exact List.mem_cons_self
        · rcases hwb' b hb with h0 | ⟨q, hq, x, hx⟩
          · exact Or.inl h0
          · refine Or.inr ⟨q, ?_, x, hx⟩
            rw [bucketBags_cons]
            exact List.mem_cons_of_mem _ hq

/-! ### The headline bound -/

/-- **Treewidth of the primal graph is at most the induced treewidth
plus one.**  Take an optimal complete elimination order
(`achievesWidth_inducedTreewidth`), dedupe it (`exists_nodup_order` —
the bags only shrink), pad it to eliminate every variable (`padOrder`
— the extra bags are empty), and run the recursive construction
(`exists_elim_treeDecomposition`).  Every bag of the resulting tree
decomposition is a recorded message scope plus at most one variable,
so its width is at most `inducedTreewidth B + 1`.  Combined with the
attained minimum, bucket elimination and graph treewidth measure the
same quantity, offset by the eliminated variable in each bag. -/
theorem treewidth_primalGraph_le [Fintype V] [∀ v, Nonempty (A v)]
    (B : List (Finset V × Set (∀ v, A v))) :
    treewidth (primalGraph B) ≤ inducedTreewidth B + 1 := by
  obtain ⟨order₀, hcov₀, hwidth₀⟩ := achievesWidth_inducedTreewidth B
  obtain ⟨order₁, hnd₁, helim₁, hbags₁⟩ := exists_nodup_order order₀
  have hcov₁ : ∀ q ∈ B, (↑q.1 : Set V) ⊆ eliminated order₁ := by
    intro q hq
    rw [helim₁]
    exact hcov₀ q hq
  have hnd : ((order₁ ++ padOrder order₁).map Sigma.fst).Nodup := by
    rw [List.map_append, List.nodup_append']
    refine ⟨hnd₁, ?_, ?_⟩
    · rw [padOrder_map_fst]
      exact (Finset.nodup_toList _).filter _
    · intro x hx₁ hx₂
      rw [padOrder_map_fst] at hx₂
      exact of_decide_eq_true (List.mem_filter.mp hx₂).2 hx₁
  have hcov : ∀ q ∈ B,
      (↑q.1 : Set V) ⊆ eliminated (order₁ ++ padOrder order₁) := by
    intro q hq
    rw [eliminated_append]
    exact (hcov₁ q hq).trans Set.subset_union_left
  have hwidth : ∀ q ∈ bucketBags (order₁ ++ padOrder order₁) B,
      q.1.card ≤ inducedTreewidth B + 1 := by
    intro q hq
    rw [bucketBags_append] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hwidth₀ q ((hbags₁ B).subset hq)
    · have h0 := bucketBags_fst_empty
        (bucketEliminate_scopes_empty hcov₁) q hq
      rw [h0, Finset.card_empty]
      omega
  obtain ⟨bags, parent, hlen, hpg, hpl, hsc, hec, hvc, hprov, hri, hwb⟩ :=
    exists_elim_treeDecomposition (order₁ ++ padOrder order₁) B hnd hcov
  have hvcover : ∀ v : V, ∃ b ∈ bags, v ∈ b := by
    intro v
    refine hvc v (mem_eliminated.mp ?_)
    rw [eliminated_append_padOrder]
    trivial
  have hcard : ∀ b ∈ bags, b.card ≤ (inducedTreewidth B + 1) + 1 := by
    intro b hb
    rcases hwb b hb with rfl | ⟨q, hq, x, rfl⟩
    · simp
    · have h1 := hwidth q hq
      have h2 := Finset.card_insert_le x q.1
      omega
  exact le_trans
    (treewidth_le_width
      ⟨bags, parent, hpg, hpl, hvcover, fun u v huv => hec u v huv, hri⟩)
    (TreeDecomposition.width_le _ hcard)

end STE
