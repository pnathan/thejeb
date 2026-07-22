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

Outlook: the running-intersection property of `elimBags` (hence
`treewidth (primalGraph B) ≤ inducedTreewidth B + 1`) is the remaining
axiom of the elimination construction; it is developed on top of these
pieces.

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
            (↑r.1 : Set V) ⊆ eliminated order := by
          intro r hr x hx
          obtain ⟨hxe, hxne⟩ := bucketStep_scope_subset p hcov r hr hx
          rcases List.mem_cons.mp (mem_eliminated.mp hxe) with h1 | h1
          · exact absurd (Set.mem_singleton_iff.mpr h1) hxne
          · exact mem_eliminated.mpr h1
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

end STE
