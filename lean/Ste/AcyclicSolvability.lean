/-
The acyclic-hypergraph master solvability theorem, hypergraph side
(Beeri–Fagin–Maier–Yannakakis direction).

**What was already mechanized, and what is new here.**  The audit of
this task expected the missing piece to be the final induction stated
over an *arbitrary* separator map.  It is not missing:
`Ste.AdaptiveConsistency.directionalConsistent_solvable` already takes
an arbitrary `sep : Fin n → Finset (Fin (n + 1))` of arbitrary
cardinality, assuming only that separators point earlier
(`hsep : ∀ i, ∀ u ∈ sep i, u.val ≤ i.val`) and that the bucket
constraints have separator scope (`SepSupported sep R`).  The chain,
tree and two-parent theorems of `Ste.Consistency`,
`Ste.ConsistencyTree` and `Ste.AdaptiveConsistency` are already its
instances.  So the *variable-elimination* half of BFMY is done.

The genuinely missing half — supplied here — is the **hypergraph
packaging**: the input of BFMY is not a separator map but a
*hypergraph* of constraint scopes, and the separators have to be
*manufactured* from it.  This file does exactly that:

* `sepOf E i` — the **canonical separator** of vertex `i` induced by a
  hyperedge family `E : Fin m → Finset (Fin (n + 1))`: the vertices
  strictly before `i` that share a hyperedge with `i`.  This is the
  earlier neighbourhood of `i` in the primal graph of the hypergraph,
  i.e. the parent set of `i` in the elimination order `0 < 1 < ⋯ < n`.
* `edge_subset_top` — the **covering lemma**: every hyperedge is
  contained in `{top k} ∪ sepOf E (top k)`, where `top k` is the
  edge's last vertex.  This is what makes hyperedge constraints
  `SepSupported` for the canonical separators
  (`edgeBucket_sepSupported`), and it holds for *every* hypergraph:
  the canonical separator is always a legal separator map.
* `edgeConsistent_solvable` — the **master hypergraph theorem**: a
  hypergraph constraint instance whose edge relations are extendable at
  their last vertex (`EdgeConsistent`, the output condition of
  semijoin/bucket processing) has a global solution.  Its proof is one
  application of `directionalConsistent_solvable` to the canonical
  separators.
* `sepWidthLE_of_sepInEdge` — where **acyclicity** finally bites.  For a
  general hypergraph the canonical separator can be large (that is the
  induced width / fill-in of the elimination order).  `SepInEdge E`
  says every `{i} ∪ sepOf E i` is *contained in a single hyperedge* —
  the running-intersection / conformality property enjoyed by
  α-acyclic hypergraphs under a GYO elimination order.  Under it the
  induced width is bounded by (max edge size − 1): elimination creates
  **no fill-in**, which is the structural content of α-acyclicity and
  the reason the BFMY algorithm is polynomial.

Corollaries, each obtained by instantiating `edgeConsistent_solvable`
with an explicit hyperedge family: the rooted-tree case
(`treeArcConsistent_solvable_of_hypergraph`, edges `{parent i, i.succ}`),
the chain case (`forwardConsistent_chain_solvable_of_hypergraph`, edges
`{i.castSucc, i.succ}`), and the two-parent case
(`twoParent_solvable_of_hypergraph`, edges `{p i, q i, i.succ}`).  Each
re-proves an existing named theorem of the library
(`treeArcConsistent_solvable`, `arcConsistent_chain_solvable`,
`twoParent_solvable`); the originals are untouched and the
subsumption is recorded in the docstrings.

**The three links formerly left open are now mechanized.**  An earlier
version of this file listed three unmechanized links of the BFMY chain
as its honest boundary; all three are proved below, sorry-free:

1. **α-acyclicity ⇒ `SepInEdge`** (`gyoReducible_sepInEdge`).  GYO /
   Graham reduction is defined as the inductive predicate `GYO` on
   states (live vertices, live edges): repeatedly delete an *ear* — a
   vertex lying in exactly one live edge — or *contract* a live edge
   whose restriction to the live vertices is contained in another's.
   `GYOReducible E` (reduction from the full state to the empty vertex
   set) yields, through the elimination listing `ElimList` and the
   domination invariant "every edge is dominated on the live vertices
   by a live edge", a permutation `π` of the vertices under which the
   reindexed hypergraph `reindex π E` satisfies `SepInEdge`: the GYO
   elimination order, reversed, is a running-intersection order with
   no fill-in.
2. **Pairwise consistency ⇒ solvability** (`pairwiseConsistent_solvable`
   and the composed headline
   `gyoReducible_pairwiseConsistent_solvable`).  The unconditional
   claim "pairwise consistency ⇒ `EdgeConsistent`" is false; the true
   BFMY statement is proved instead: on a hypergraph satisfying the
   running-intersection property (`SepInEdge`) — in the headline, on
   any GYO-reducible hypergraph — pairwise-consistent
   (semijoin-reduced) nonempty edge relations admit a global solution.
   `PairwiseConsistent` is the output condition of a full semijoin
   pass: every domain-respecting tuple of each relation matches some
   tuple of every other relation on the shared attributes.  The proof
   is the textbook greedy sweep: the invariant "the assigned prefix of
   every edge extends to a full tuple of that edge" is propagated
   using the cover edge that `SepInEdge` provides at each vertex.
3. **One bucket per vertex removed** (`edgeConsistent_solvable'`).
   The master theorem is restated without `htop_inj` by grouping the
   edges topped at each vertex into a single bucket edge
   `insert i (⋃ top k = i, E k)` with the conjunctive relation
   `∀ k, top k = i → Rel k`; the hypothesis becomes
   `BucketEdgeConsistent` — simultaneous extendability of each bucket
   — which `EdgeConsistent.bucketEdgeConsistent` recovers from
   `EdgeConsistent` when `top` *is* injective, so the original theorem
   is the injective special case.

**Honest residue.**  (1) `GYO` is one standard presentation of Graham
reduction; its equivalence with other definitions of α-acyclicity
(join-tree existence, conformal + chordal primal graph, Bachman
diagrams) is not mechanized, and only the direction "GYO-reducible ⇒
running-intersection order exists" is proved — the converse is not
needed for solvability and is not claimed.  (2) The ear rule requires
the vertex to lie in *some* live edge, so a hypergraph with a vertex
in no edge at all is not `GYOReducible`; this is forced, since
`SepInEdge` itself demands that every vertex lie in an edge.  (3) That
`PairwiseConsistent` can be *enforced* by a polynomial semijoin
program (the algorithmic half of BFMY) is not modelled, exactly as the
enforcement of `DirectionalConsistent` is out of scope in
`Ste.AdaptiveConsistency`.  (4) The solvability direction only:
`pairwiseConsistent_solvable` does not prove the converse BFMY
direction that acyclicity is *necessary* for pairwise consistency to
imply global consistency.

There is no `sorry` in this file: every statement made is proved.

References: C. Beeri, R. Fagin, D. Maier, M. Yannakakis, *On the
desirability of acyclic database schemes*, JACM 30(3):479–513, 1983
(`beeri1983acyclic`); E. C. Freuder, *A Sufficient Condition for
Backtrack-Free Search*, JACM 29(1):24–32, 1982
(`freuder1982backtrack`); R. Dechter, *Constraint Processing*, Morgan
Kaufmann, 2003, ch. 4 (`dechter2003constraint`).
-/
import Mathlib.Data.Finset.Card
import Ste.AdaptiveConsistency

namespace STE

open Set

variable {α : Type*}

/-! ### The canonical separator of a hyperedge family -/

/-- **The canonical separator** of vertex `i` induced by the hyperedge
family `E`: the vertices strictly earlier than `i` that share a
hyperedge with `i`.  Equivalently, the earlier neighbourhood of `i` in
the primal graph of the hypergraph — the parent set of `i` for the
elimination order `0 < 1 < ⋯ < n`. -/
def sepOf {m n : ℕ} (E : Fin m → Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun j => j < i ∧ ∃ k, i ∈ E k ∧ j ∈ E k)

theorem mem_sepOf {m n : ℕ} (E : Fin m → Finset (Fin (n + 1)))
    {i j : Fin (n + 1)} :
    j ∈ sepOf E i ↔ j < i ∧ ∃ k, i ∈ E k ∧ j ∈ E k := by
  simp [sepOf, Finset.mem_filter]

/-- Canonical separators point strictly earlier. -/
theorem sepOf_lt {m n : ℕ} (E : Fin m → Finset (Fin (n + 1)))
    {i j : Fin (n + 1)} (h : j ∈ sepOf E i) : j < i :=
  ((mem_sepOf E).mp h).1

/-- Canonical separators satisfy the topological-order hypothesis of
`Ste.AdaptiveConsistency`: every member of `sepOf E i.succ` has index
`≤ i`. -/
theorem sepOf_succ_le {m n : ℕ} (E : Fin m → Finset (Fin (n + 1)))
    (i : Fin n) : ∀ u ∈ sepOf E i.succ, u.val ≤ i.val := by
  intro u hu
  have h : u.val < (i.succ).val := (Fin.lt_def).mp (sepOf_lt E hu)
  rw [Fin.val_succ] at h
  omega

/-- **The covering lemma** — the reason canonical separators are legal
separators.  If `top k` is the last vertex of hyperedge `k`, then the
whole edge lives inside `{top k} ∪ sepOf E (top k)`.  No acyclicity is
needed: this holds for every hypergraph. -/
theorem edge_subset_top {m n : ℕ} (E : Fin m → Finset (Fin (n + 1)))
    (top : Fin m → Fin (n + 1)) (htop_mem : ∀ k, top k ∈ E k)
    (htop_le : ∀ k, ∀ j ∈ E k, j ≤ top k) (k : Fin m) :
    E k ⊆ insert (top k) (sepOf E (top k)) := by
  intro j hj
  rcases eq_or_ne j (top k) with rfl | hne
  · exact Finset.mem_insert_self _ _
  · refine Finset.mem_insert_of_mem ?_
    exact (mem_sepOf E).mpr
      ⟨lt_of_le_of_ne (htop_le k j hj) hne, ⟨k, htop_mem k, hj⟩⟩

/-! ### Hypergraph constraint instances -/

/-- **Edge scope**: the relation `Rel k` reads only the vertices of its
hyperedge `E k`.  This is the hypergraph form of `SepSupported`. -/
def EdgeSupported {m n : ℕ} (E : Fin m → Finset (Fin (n + 1)))
    (Rel : Fin m → (Fin (n + 1) → α) → Prop) : Prop :=
  ∀ k : Fin m, ∀ g g' : Fin (n + 1) → α,
    (∀ u ∈ E k, g u = g' u) → (Rel k g ↔ Rel k g')

/-- The bucket of vertex `i.succ`: the conjunction of the relations of
all hyperedges whose last vertex is `i.succ`. -/
def edgeBucket {m n : ℕ} (Rel : Fin m → (Fin (n + 1) → α) → Prop)
    (top : Fin m → Fin (n + 1)) (i : Fin n) (g : Fin (n + 1) → α) : Prop :=
  ∀ k : Fin m, top k = i.succ → Rel k g

/-- Hyperedge relations are `SepSupported` for the canonical
separators — by the covering lemma, a bucket can only see its vertex
and that vertex's canonical separator. -/
theorem edgeBucket_sepSupported {m n : ℕ}
    (E : Fin m → Finset (Fin (n + 1))) (top : Fin m → Fin (n + 1))
    (Rel : Fin m → (Fin (n + 1) → α) → Prop)
    (htop_mem : ∀ k, top k ∈ E k)
    (htop_le : ∀ k, ∀ j ∈ E k, j ≤ top k)
    (hsupp : EdgeSupported E Rel) :
    SepSupported (fun i : Fin n => sepOf E i.succ) (edgeBucket Rel top) := by
  intro i g g' hs hsucc
  have key : ∀ k : Fin m, top k = i.succ → ∀ u ∈ E k, g u = g' u := by
    intro k hk u hu
    have hmem := edge_subset_top E top htop_mem htop_le k hu
    rw [hk] at hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · subst h; exact hsucc
    · exact hs u h
  exact ⟨fun h k hk => (hsupp k g g' (key k hk)).mp (h k hk),
    fun h k hk => (hsupp k g g' (key k hk)).mpr (h k hk)⟩

/-- **Edge extendability** — the hypergraph form of directional
consistency, and the output condition of a semijoin / bucket-processing
pass: every domain-respecting assignment can be repaired at the last
vertex of edge `k` so as to satisfy `Rel k`. -/
def EdgeConsistent {m n : ℕ} (D : Fin (n + 1) → Set α)
    (Rel : Fin m → (Fin (n + 1) → α) → Prop)
    (top : Fin m → Fin (n + 1)) : Prop :=
  ∀ k : Fin m, ∀ g : Fin (n + 1) → α, (∀ u, g u ∈ D u) →
    ∃ c ∈ D (top k), Rel k (Function.update g (top k) c)

/-- Every nonzero vertex of `Fin (n + 1)` is a successor. -/
theorem exists_succ_of_ne_zero {n : ℕ} {v : Fin (n + 1)} (h : v ≠ 0) :
    ∃ i : Fin n, v = i.succ := by
  cases n with
  | zero => exact absurd (Fin.eq_zero v) h
  | succ m =>
    cases v using Fin.cases with
    | zero => exact absurd rfl h
    | succ j => exact ⟨j, rfl⟩

/-! ### The master hypergraph solvability theorem -/

/-- **Master theorem (BFMY direction, hypergraph form).**  Let the
constraint scopes be the hyperedges `E : Fin m → Finset (Fin (n + 1))`,
each edge `k` carrying a relation `Rel k` of scope `E k`
(`hsupp`) and a last vertex `top k` (`htop_mem`, `htop_le`), with at
most one edge per last vertex (`htop_inj`).  If the relations are
extendable at their last vertex (`EdgeConsistent`) and the edges topped
at the root are absorbed into the root domain (`hzero`), then the
instance has a global solution: an assignment in all domains
satisfying all edge relations.

The proof is a single application of
`Ste.AdaptiveConsistency.directionalConsistent_solvable` to the
canonical separators `sepOf E`, which the covering lemma
`edge_subset_top` certifies as a legal separator map for *any*
hypergraph.  Acyclicity is not needed for solvability; it is needed to
bound the induced width (`sepWidthLE_of_sepInEdge`), i.e. to make
enforcing `EdgeConsistent` cheap. -/
theorem edgeConsistent_solvable {m n : ℕ} {D : Fin (n + 1) → Set α}
    {E : Fin m → Finset (Fin (n + 1))}
    {Rel : Fin m → (Fin (n + 1) → α) → Prop}
    {top : Fin m → Fin (n + 1)}
    (htop_mem : ∀ k, top k ∈ E k)
    (htop_le : ∀ k, ∀ j ∈ E k, j ≤ top k)
    (hsupp : EdgeSupported E Rel)
    (htop_inj : Function.Injective top)
    (hEC : EdgeConsistent D Rel top)
    (hzero : ∀ k, top k = 0 → ∀ g : Fin (n + 1) → α, g 0 ∈ D 0 → Rel k g)
    (hne : ∀ u, (D u).Nonempty) :
    ∃ f : Fin (n + 1) → α, (∀ u, f u ∈ D u) ∧ ∀ k, Rel k f := by
  have hDC : DirectionalConsistent D (edgeBucket Rel top) := by
    intro i g hg
    by_cases hex : ∃ k, top k = i.succ
    · obtain ⟨k₀, hk₀⟩ := hex
      obtain ⟨c, hc, hRc⟩ := hEC k₀ g hg
      rw [hk₀] at hc hRc
      refine ⟨c, hc, ?_⟩
      intro k hk
      have hkk : k = k₀ := htop_inj (by rw [hk, hk₀])
      subst hkk
      exact hRc
    · obtain ⟨c, hc⟩ := hne i.succ
      exact ⟨c, hc, fun k hk => absurd ⟨k, hk⟩ hex⟩
  obtain ⟨f, hf⟩ :=
    directionalConsistent_solvable (sep := fun i : Fin n => sepOf E i.succ)
      (sepOf_succ_le E)
      (edgeBucket_sepSupported E top Rel htop_mem htop_le hsupp) hDC hne
  refine ⟨f, hf.1, ?_⟩
  intro k
  rcases eq_or_ne (top k) 0 with h0 | h0
  · exact hzero k h0 f (hf.1 0)
  · obtain ⟨i, hi⟩ := exists_succ_of_ne_zero h0
    exact hf.2 i k hi

/-! ### Where acyclicity bites: no fill-in -/

/-- **The running-intersection / conformality property** enjoyed by
α-acyclic hypergraphs under a GYO elimination order: the closed
canonical separator `{i} ∪ sepOf E i` of every vertex is contained in a
single hyperedge.  Equivalently: eliminating the vertices in the order
`n, n - 1, …, 0` creates no fill-in edge. -/
def SepInEdge {m n : ℕ} (E : Fin m → Finset (Fin (n + 1))) : Prop :=
  ∀ i : Fin (n + 1), ∃ k, insert i (sepOf E i) ⊆ E k

/-- **Acyclicity bounds the induced width.**  If the elimination order
creates no fill-in (`SepInEdge`) and every hyperedge has at most `w + 1`
vertices, then every canonical separator has at most `w` members — the
network has induced width `≤ w` in the sense of
`Ste.AdaptiveConsistency.SepWidthLE`.  This is why BFMY's algorithm is
polynomial on α-acyclic schemes: the buckets never grow beyond the
original relations. -/
theorem sepWidthLE_of_sepInEdge {m n w : ℕ} {E : Fin m → Finset (Fin (n + 1))}
    (h : SepInEdge E) (hcard : ∀ k, (E k).card ≤ w + 1) :
    SepWidthLE (fun i : Fin n => sepOf E i.succ) w := by
  intro i
  show (sepOf E i.succ).card ≤ w
  obtain ⟨k, hk⟩ := h i.succ
  have hmem : i.succ ∈ E k := hk (Finset.mem_insert_self _ _)
  have hsub : sepOf E i.succ ⊆ (E k).erase i.succ := by
    intro u hu
    exact Finset.mem_erase.mpr
      ⟨ne_of_lt (sepOf_lt E hu), hk (Finset.mem_insert_of_mem hu)⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hmem] at hle
  have hpos : 1 ≤ (E k).card := Finset.card_pos.mpr ⟨_, hmem⟩
  have := hcard k
  omega

/-! ### Corollary (b): the rooted-tree case, edges `{parent i, i.succ}` -/

/-- **The tree theorem as a hypergraph instance.**  Taking the
hyperedges to be the tree edges `E i = {parent i, i.succ}`, each topped
at `i.succ`, the master theorem re-proves
`Ste.ConsistencyTree.treeArcConsistent_solvable` (and its
`Ste.AdaptiveConsistency` re-derivation
`treeArcConsistent_solvable_of_adaptive`).  Those originals are
unchanged; this is the BFMY packaging of the same fact — a tree is the
α-acyclic hypergraph whose edges are all of size 2. -/
theorem treeArcConsistent_solvable_of_hypergraph {n : ℕ}
    {D : Fin (n + 1) → Set α} {parent : Fin n → Fin (n + 1)}
    {R : Fin n → α → α → Prop}
    (hpar : ∀ i, (parent i).val ≤ i.val)
    (hAC : TreeArcConsistent D parent R) (hne : ∀ u, (D u).Nonempty) :
    ∃ f, TreeSolution D parent R f := by
  set E : Fin n → Finset (Fin (n + 1)) := fun i => {parent i, i.succ} with hE
  have hpne : ∀ i : Fin n, parent i ≠ i.succ := by
    intro i h
    have h1 := hpar i
    rw [h, Fin.val_succ] at h1
    omega
  have htop_mem : ∀ k : Fin n, k.succ ∈ E k := by
    intro k
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have htop_le : ∀ k : Fin n, ∀ j ∈ E k, j ≤ k.succ := by
    intro k j hj
    rcases Finset.mem_insert.mp hj with h | h
    · subst h
      exact (Fin.le_def).mpr (by rw [Fin.val_succ]; have := hpar k; omega)
    · rw [Finset.mem_singleton] at h
      subst h
      exact le_rfl
  have hsupp : EdgeSupported E (fun i g => R i (g (parent i)) (g i.succ)) := by
    intro k g g' hagree
    show R k (g (parent k)) (g k.succ) ↔ R k (g' (parent k)) (g' k.succ)
    rw [hagree (parent k) (Finset.mem_insert_self _ _),
      hagree k.succ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))]
  have hEC : EdgeConsistent D (fun i g => R i (g (parent i)) (g i.succ))
      Fin.succ := by
    intro k g hg
    obtain ⟨c, hc, hRc⟩ := hAC k (g (parent k)) (hg (parent k))
    refine ⟨c, hc, ?_⟩
    show R k (Function.update g k.succ c (parent k))
      (Function.update g k.succ c k.succ)
    rw [Function.update_of_ne (hpne k), Function.update_self]
    exact hRc
  obtain ⟨f, hfD, hfR⟩ :=
    edgeConsistent_solvable (E := E) (top := Fin.succ) htop_mem htop_le hsupp
      (Fin.succ_injective n) hEC
      (fun k hk => absurd hk (Fin.succ_ne_zero k)) hne
  exact ⟨f, hfD, hfR⟩

/-! ### Corollary (a): the chain case, edges `{i.castSucc, i.succ}` -/

/-- **The chain theorem as a hypergraph instance**: the path hypergraph
`E i = {i.castSucc, i.succ}`.  This re-proves
`Ste.Consistency.arcConsistent_chain_solvable`, which is left
untouched.  (The original `forwardConsistent_chain_solvable` needs only
the *root* domain nonempty; the hypergraph route, going through
`directionalConsistent_solvable`, needs all domains nonempty — the
`hne` gap documented in `Ste.AdaptiveConsistency`'s honest scope.) -/
theorem forwardConsistent_chain_solvable_of_hypergraph {n : ℕ}
    {D : Fin (n + 1) → Set α} {R : Fin n → α → α → Prop}
    (hFC : ForwardConsistent D R) (hne : ∀ u, (D u).Nonempty) :
    ∃ f, ChainSolution D R f := by
  have hpar : ∀ i : Fin n, (Fin.castSucc i).val ≤ i.val := fun i => le_rfl
  have hAC : TreeArcConsistent D Fin.castSucc R := hFC
  obtain ⟨f, hfD, hfR⟩ :=
    treeArcConsistent_solvable_of_hypergraph hpar hAC hne
  exact ⟨f, hfD, hfR⟩

/-! ### Corollary (c): the two-parent (properly cyclic) case,
edges `{p i, q i, i.succ}` -/

/-- **The two-parent theorem as a hypergraph instance**: the hyperedges
are the triangles `E i = {p i, q i, i.succ}`, the smallest genuinely
cyclic primal graphs.  This re-proves
`Ste.AdaptiveConsistency.twoParent_solvable`, which is left untouched;
here the separator is *computed* from the hypergraph rather than
supplied. -/
theorem twoParent_solvable_of_hypergraph {n : ℕ}
    {D : Fin (n + 1) → Set α} {p q : Fin n → Fin (n + 1)}
    {R : Fin n → α → α → α → Prop}
    (hp : ∀ i, (p i).val ≤ i.val) (hq : ∀ i, (q i).val ≤ i.val)
    (hDC : ∀ i : Fin n, ∀ g : Fin (n + 1) → α, (∀ u, g u ∈ D u) →
      ∃ c ∈ D i.succ, R i (g (p i)) (g (q i)) c)
    (hne : ∀ u, (D u).Nonempty) :
    ∃ f : Fin (n + 1) → α, (∀ u, f u ∈ D u) ∧
      ∀ i : Fin n, R i (f (p i)) (f (q i)) (f i.succ) := by
  set E : Fin n → Finset (Fin (n + 1)) := fun i => {p i, q i, i.succ} with hE
  have hpne : ∀ i : Fin n, p i ≠ i.succ := by
    intro i h
    have h1 := hp i
    rw [h, Fin.val_succ] at h1
    omega
  have hqne : ∀ i : Fin n, q i ≠ i.succ := by
    intro i h
    have h1 := hq i
    rw [h, Fin.val_succ] at h1
    omega
  have hmp : ∀ k : Fin n, p k ∈ E k := fun k => Finset.mem_insert_self _ _
  have hmq : ∀ k : Fin n, q k ∈ E k := fun k =>
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have htop_mem : ∀ k : Fin n, k.succ ∈ E k := fun k =>
    Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have htop_le : ∀ k : Fin n, ∀ j ∈ E k, j ≤ k.succ := by
    intro k j hj
    rcases Finset.mem_insert.mp hj with h | h
    · subst h
      exact (Fin.le_def).mpr (by rw [Fin.val_succ]; have := hp k; omega)
    · rcases Finset.mem_insert.mp h with h' | h'
      · subst h'
        exact (Fin.le_def).mpr (by rw [Fin.val_succ]; have := hq k; omega)
      · rw [Finset.mem_singleton] at h'
        subst h'
        exact le_rfl
  have hsupp : EdgeSupported E
      (fun i g => R i (g (p i)) (g (q i)) (g i.succ)) := by
    intro k g g' hagree
    show R k (g (p k)) (g (q k)) (g k.succ) ↔
      R k (g' (p k)) (g' (q k)) (g' k.succ)
    rw [hagree (p k) (hmp k), hagree (q k) (hmq k),
      hagree k.succ (htop_mem k)]
  have hEC : EdgeConsistent D
      (fun i g => R i (g (p i)) (g (q i)) (g i.succ)) Fin.succ := by
    intro k g hg
    obtain ⟨c, hc, hRc⟩ := hDC k g hg
    refine ⟨c, hc, ?_⟩
    show R k (Function.update g k.succ c (p k))
      (Function.update g k.succ c (q k))
      (Function.update g k.succ c k.succ)
    rw [Function.update_of_ne (hpne k), Function.update_of_ne (hqne k),
      Function.update_self]
    exact hRc
  obtain ⟨f, hfD, hfR⟩ :=
    edgeConsistent_solvable (E := E) (top := Fin.succ) htop_mem htop_le hsupp
      (Fin.succ_injective n) hEC
      (fun k hk => absurd hk (Fin.succ_ne_zero k)) hne
  exact ⟨f, hfD, hfR⟩

/-! ### Consistency check against the originals

Each corollary above has exactly the statement of the corresponding
existing theorem, so the originals follow from the hypergraph
packaging.  These `example`s record the subsumption without touching
the original files. -/

example {n : ℕ} {D : Fin (n + 1) → Set α} {parent : Fin n → Fin (n + 1)}
    {R : Fin n → α → α → Prop} (hpar : ∀ i, (parent i).val ≤ i.val)
    (hAC : TreeArcConsistent D parent R) (hne : ∀ u, (D u).Nonempty) :
    ∃ f, TreeSolution D parent R f :=
  treeArcConsistent_solvable_of_hypergraph hpar hAC hne

example {n : ℕ} {D : Fin (n + 1) → Set α} {R : Fin n → α → α → Prop}
    (hAC : ArcConsistent D R) (hne : ∀ i, (D i).Nonempty) :
    ∃ f : Fin (n + 1) → α,
      (∀ i, f i ∈ D i) ∧ ∀ i : Fin n, R i (f i.castSucc) (f i.succ) :=
  forwardConsistent_chain_solvable_of_hypergraph hAC.1 hne

/-! ### Removing top-injectivity: one bucket per vertex, by grouping

`edgeConsistent_solvable` assumes `top` injective, so that each vertex
tops at most one edge.  Grouping the edges topped at a vertex into a
single *bucket edge* — `insert i (⋃ top k = i, E k)`, carrying the
conjunction of their relations — produces an instance whose top map is
the identity, trivially injective, and the master theorem applies.
The price is that extendability must be stated for the whole bucket
(`BucketEdgeConsistent`); when `top` is injective this is the old
`EdgeConsistent` (`EdgeConsistent.bucketEdgeConsistent`), so the
grouped theorem `edgeConsistent_solvable'` strictly subsumes the
original. -/

/-- **Bucketed edge extendability**: every domain-respecting
assignment can be repaired at vertex `i` so as to satisfy *all* the
edge relations topped at `i` simultaneously.  This is the honest form
of the semijoin/bucket-processing output condition when several edges
share a last vertex; for injective `top` it coincides with
`EdgeConsistent` (`EdgeConsistent.bucketEdgeConsistent`). -/
def BucketEdgeConsistent {m n : ℕ} (D : Fin (n + 1) → Set α)
    (Rel : Fin m → (Fin (n + 1) → α) → Prop)
    (top : Fin m → Fin (n + 1)) : Prop :=
  ∀ i : Fin (n + 1), ∀ g : Fin (n + 1) → α, (∀ u, g u ∈ D u) →
    ∃ c ∈ D i, ∀ k, top k = i → Rel k (Function.update g i c)

/-- With an injective `top`, per-edge extendability is bucketed
extendability: each bucket holds at most one edge. -/
theorem EdgeConsistent.bucketEdgeConsistent {m n : ℕ}
    {D : Fin (n + 1) → Set α} {Rel : Fin m → (Fin (n + 1) → α) → Prop}
    {top : Fin m → Fin (n + 1)} (htop_inj : Function.Injective top)
    (hEC : EdgeConsistent D Rel top) (hne : ∀ u, (D u).Nonempty) :
    BucketEdgeConsistent D Rel top := by
  intro i g hg
  by_cases hex : ∃ k, top k = i
  · obtain ⟨k₀, hk₀⟩ := hex
    obtain ⟨c, hc, hRc⟩ := hEC k₀ g hg
    rw [hk₀] at hc hRc
    refine ⟨c, hc, ?_⟩
    intro k hk
    have hkk : k = k₀ := htop_inj (by rw [hk, hk₀])
    subst hkk
    exact hRc
  · obtain ⟨c, hc⟩ := hne i
    exact ⟨c, hc, fun k hk => absurd ⟨k, hk⟩ hex⟩

/-- **Master theorem without top-injectivity.**  The hypotheses of
`edgeConsistent_solvable` minus `htop_inj`, with `EdgeConsistent`
strengthened to its bucketed form `BucketEdgeConsistent`.  Proof:
group the edges topped at each vertex `i` into the bucket edge
`insert i {j | ∃ k, top k = i ∧ j ∈ E k}` carrying the conjunctive
relation `∀ k, top k = i → Rel k`, whose top map is the identity, and
apply `edgeConsistent_solvable` to the grouped instance.  The original
theorem is the injective special case via
`EdgeConsistent.bucketEdgeConsistent`. -/
theorem edgeConsistent_solvable' {m n : ℕ} {D : Fin (n + 1) → Set α}
    {E : Fin m → Finset (Fin (n + 1))}
    {Rel : Fin m → (Fin (n + 1) → α) → Prop}
    {top : Fin m → Fin (n + 1)}
    (_htop_mem : ∀ k, top k ∈ E k)
    (htop_le : ∀ k, ∀ j ∈ E k, j ≤ top k)
    (hsupp : EdgeSupported E Rel)
    (hBEC : BucketEdgeConsistent D Rel top)
    (hzero : ∀ k, top k = 0 → ∀ g : Fin (n + 1) → α, g 0 ∈ D 0 → Rel k g)
    (hne : ∀ u, (D u).Nonempty) :
    ∃ f : Fin (n + 1) → α, (∀ u, f u ∈ D u) ∧ ∀ k, Rel k f := by
  set E' : Fin (n + 1) → Finset (Fin (n + 1)) := fun i =>
    insert i (Finset.univ.filter fun j => ∃ k, top k = i ∧ j ∈ E k)
    with hE'
  set Rel' : Fin (n + 1) → (Fin (n + 1) → α) → Prop :=
    fun i g => ∀ k, top k = i → Rel k g with hRel'
  have hEsub : ∀ k, E k ⊆ E' (top k) := by
    intro k j hj
    rcases eq_or_ne j (top k) with rfl | hjne
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, rfl, hj⟩)
  have htop_mem' : ∀ i : Fin (n + 1), (id i : Fin (n + 1)) ∈ E' i :=
    fun i => Finset.mem_insert_self _ _
  have htop_le' : ∀ i : Fin (n + 1), ∀ j ∈ E' i, j ≤ id i := by
    intro i j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact le_rfl
    · obtain ⟨-, k, hk, hjk⟩ := Finset.mem_filter.mp hj
      show j ≤ i
      rw [← hk]
      exact htop_le k j hjk
  have hsupp' : EdgeSupported E' Rel' := by
    intro i g g' hagree
    have key : ∀ k, top k = i → ∀ u ∈ E k, g u = g' u :=
      fun k hk u hu => hagree u (hk ▸ hEsub k hu)
    exact ⟨fun h k hk => (hsupp k g g' (key k hk)).mp (h k hk),
      fun h k hk => (hsupp k g g' (key k hk)).mpr (h k hk)⟩
  have hEC' : EdgeConsistent D Rel' id := fun i g hg => hBEC i g hg
  have hzero' : ∀ i : Fin (n + 1), id i = 0 →
      ∀ g : Fin (n + 1) → α, g 0 ∈ D 0 → Rel' i g :=
    fun i hi g hg k hk => hzero k (hk.trans hi) g hg
  obtain ⟨f, hfD, hfR⟩ := edgeConsistent_solvable (E := E') (top := id)
    htop_mem' htop_le' hsupp' Function.injective_id hEC' hzero' hne
  exact ⟨f, hfD, fun k => hfR (top k) k rfl⟩

/-- Sanity: the original master theorem is re-derived from the
bucketed one — top-injectivity is gone for good. -/
example {m n : ℕ} {D : Fin (n + 1) → Set α}
    {E : Fin m → Finset (Fin (n + 1))}
    {Rel : Fin m → (Fin (n + 1) → α) → Prop}
    {top : Fin m → Fin (n + 1)}
    (htop_mem : ∀ k, top k ∈ E k)
    (htop_le : ∀ k, ∀ j ∈ E k, j ≤ top k)
    (hsupp : EdgeSupported E Rel)
    (htop_inj : Function.Injective top)
    (hEC : EdgeConsistent D Rel top)
    (hzero : ∀ k, top k = 0 → ∀ g : Fin (n + 1) → α, g 0 ∈ D 0 → Rel k g)
    (hne : ∀ u, (D u).Nonempty) :
    ∃ f : Fin (n + 1) → α, (∀ u, f u ∈ D u) ∧ ∀ k, Rel k f :=
  edgeConsistent_solvable' htop_mem htop_le hsupp
    (hEC.bucketEdgeConsistent htop_inj hne) hzero hne

/-! ### GYO / Graham reduction ⇒ a running-intersection order

α-acyclicity enters the file as `SepInEdge` — the no-fill-in property
of the ambient order `0 < 1 < ⋯ < n`.  Here that property is *derived*
from GYO (Graham) reduction: `GYO E S K` reduces the state of live
vertices `S` and live edges `K` by deleting an **ear** (a vertex lying
in exactly one live edge) or **contracting** a live edge dominated on
`S` by another live edge, down to `S = ∅`.  A `GYOReducible`
hypergraph yields an elimination listing (`ElimList`, via the
invariant that every edge is dominated on the live vertices by a live
edge), whose reversal is a vertex order with the running-intersection
property — i.e. a permutation `π` with `SepInEdge (reindex π E)`
(`gyoReducible_sepInEdge`). -/

/-- **GYO (Graham) reduction** on states `(S, K)` of live vertices and
live edges (edges are implicitly restricted to `S`):

* `empty` — the empty vertex set is fully reduced;
* `ear` — delete a vertex `v ∈ S` lying in exactly one live edge `k₀`
  (all of `v`'s live occurrences are in `E k₀`);
* `contract` — delete a live edge `k` whose restriction to `S` is
  contained in that of another live edge `k'`.

This is the classical reduction whose success characterizes
α-acyclicity (`beeri1983acyclic`). -/
inductive GYO {m n : ℕ} (E : Fin m → Finset (Fin (n + 1))) :
    Finset (Fin (n + 1)) → Finset (Fin m) → Prop
  | empty (K : Finset (Fin m)) : GYO E ∅ K
  | ear {S : Finset (Fin (n + 1))} {K : Finset (Fin m)}
      {v : Fin (n + 1)} {k₀ : Fin m}
      (hv : v ∈ S) (hk₀ : k₀ ∈ K) (hvk₀ : v ∈ E k₀)
      (honly : ∀ k ∈ K, v ∈ E k → k = k₀)
      (h : GYO E (S.erase v) K) : GYO E S K
  | contract {S : Finset (Fin (n + 1))} {K : Finset (Fin m)}
      {k k' : Fin m}
      (hk : k ∈ K) (hk' : k' ∈ K) (hne : k' ≠ k)
      (hsub : E k ∩ S ⊆ E k' ∩ S)
      (h : GYO E S (K.erase k)) : GYO E S K

/-- **GYO-reducibility (α-acyclicity, GYO form)**: the full state —
all vertices, all edges — reduces to the empty vertex set. -/
def GYOReducible {m n : ℕ} (E : Fin m → Finset (Fin (n + 1))) : Prop :=
  GYO E Finset.univ Finset.univ

/-- **An elimination listing**: the vertices in elimination order
(first eliminated at the head).  At each step the eliminated vertex
`v` lies in an edge `E k` that contains every not-yet-eliminated
neighbour of `v` — the step-wise running-intersection property.  The
*reversal* of such a listing is a vertex order with `SepInEdge`. -/
inductive ElimList {m n : ℕ} (E : Fin m → Finset (Fin (n + 1))) :
    List (Fin (n + 1)) → Prop
  | nil : ElimList E []
  | cons {v : Fin (n + 1)} {rest : List (Fin (n + 1))} (k : Fin m)
      (hvk : v ∈ E k)
      (hcov : ∀ u ∈ rest, (∃ k', v ∈ E k' ∧ u ∈ E k') → u ∈ E k)
      (h : ElimList E rest) : ElimList E (v :: rest)

/-- **GYO reduction produces an elimination listing.**  The invariant
carried down the derivation — every edge (dead or alive) is dominated
on the live vertices by a live edge — turns the ear condition ("`v`
lies in exactly one live edge") into the listing condition ("some
single edge contains all of `v`'s remaining neighbours"): a neighbour
witnessed by *any* edge is a neighbour witnessed by a live edge, and
the only live edge containing `v` is the ear's edge.  Contraction
preserves the invariant because the removed edge's dominator remains
live. -/
theorem gyo_elimList {m n : ℕ} {E : Fin m → Finset (Fin (n + 1))} :
    ∀ {S : Finset (Fin (n + 1))} {K : Finset (Fin m)}, GYO E S K →
      (∀ k, ∃ k' ∈ K, E k ∩ S ⊆ E k' ∩ S) →
      ∃ L : List (Fin (n + 1)),
        ElimList E L ∧ L.Nodup ∧ ∀ x, x ∈ L ↔ x ∈ S := by
  intro S K h
  induction h with
  | empty K =>
      intro _
      exact ⟨[], .nil, List.nodup_nil, fun x => by simp⟩
  | @ear S K v k₀ hv hk₀ hvk₀ honly h ih =>
      intro hinv
      obtain ⟨L, hL, hnd, hmem⟩ := ih (by
        intro k
        obtain ⟨k', hk', hsub⟩ := hinv k
        refine ⟨k', hk', fun x hx => ?_⟩
        obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
        obtain ⟨hxv, hxS⟩ := Finset.mem_erase.mp hx2
        have hx3 := hsub (Finset.mem_inter.mpr ⟨hx1, hxS⟩)
        obtain ⟨hx4, hx5⟩ := Finset.mem_inter.mp hx3
        exact Finset.mem_inter.mpr ⟨hx4, Finset.mem_erase.mpr ⟨hxv, hx5⟩⟩)
      refine ⟨v :: L, .cons k₀ hvk₀ ?_ hL, ?_, ?_⟩
      · rintro u hu ⟨k', hvk', huk'⟩
        obtain ⟨kl, hkl, hsub⟩ := hinv k'
        have hvkl : v ∈ E kl :=
          (Finset.mem_inter.mp (hsub (Finset.mem_inter.mpr ⟨hvk', hv⟩))).1
        have hkl₀ : kl = k₀ := honly kl hkl hvkl
        subst hkl₀
        have huS : u ∈ S := Finset.mem_of_mem_erase ((hmem u).mp hu)
        exact (Finset.mem_inter.mp
          (hsub (Finset.mem_inter.mpr ⟨huk', huS⟩))).1
      · exact List.nodup_cons.mpr
          ⟨fun hvL => (Finset.mem_erase.mp ((hmem v).mp hvL)).1 rfl, hnd⟩
      · intro x
        rw [List.mem_cons, hmem x, Finset.mem_erase]
        constructor
        · rintro (rfl | ⟨-, hx⟩)
          exacts [hv, hx]
        · intro hx
          rcases eq_or_ne x v with rfl | hxv
          · exact Or.inl rfl
          · exact Or.inr ⟨hxv, hx⟩
  | @contract S K k k' hk hk' hne hsub h ih =>
      intro hinv
      refine ih ?_
      intro e
      obtain ⟨e', he', hesub⟩ := hinv e
      rcases eq_or_ne e' k with rfl | hene
      · exact ⟨k', Finset.mem_erase.mpr ⟨hne, hk'⟩, hesub.trans hsub⟩
      · exact ⟨e', Finset.mem_erase.mpr ⟨hene, he'⟩, hesub⟩

/-- Positional form of the listing property: at each position `a`,
some edge contains the vertex at `a` and every later-listed neighbour
of it. -/
theorem ElimList.property {m n : ℕ} {E : Fin m → Finset (Fin (n + 1))} :
    ∀ {L : List (Fin (n + 1))}, ElimList E L →
      ∀ (a : ℕ) (ha : a < L.length),
        ∃ k, L.get ⟨a, ha⟩ ∈ E k ∧
          ∀ (b : ℕ) (hb : b < L.length), a < b →
            (∃ k', L.get ⟨a, ha⟩ ∈ E k' ∧ L.get ⟨b, hb⟩ ∈ E k') →
            L.get ⟨b, hb⟩ ∈ E k := by
  intro L h
  induction h with
  | nil =>
      intro a ha
      simp at ha
  | @cons v rest k hvk hcov h ih =>
      intro a ha
      cases a with
      | zero =>
          refine ⟨k, hvk, ?_⟩
          intro b hb hab hsh
          cases b with
          | zero => omega
          | succ b =>
              have hb' : b < rest.length := by
                simp only [List.length_cons] at hb
                omega
              exact hcov _ (List.get_mem rest ⟨b, hb'⟩) hsh
      | succ a =>
          have ha' : a < rest.length := by
            simp only [List.length_cons] at ha
            omega
          obtain ⟨k', hk'1, hk'2⟩ := ih a ha'
          refine ⟨k', hk'1, ?_⟩
          intro b hb hab hsh
          cases b with
          | zero => omega
          | succ b =>
              have hb' : b < rest.length := by
                simp only [List.length_cons] at hb
                omega
              exact hk'2 b hb' (by omega) hsh

/-- **Reindexing a hyperedge family** along a permutation of the
vertices: position `j` of the reindexed hypergraph carries vertex
`π j` of the original. -/
def reindex {m n : ℕ} (π : Equiv.Perm (Fin (n + 1)))
    (E : Fin m → Finset (Fin (n + 1))) : Fin m → Finset (Fin (n + 1)) :=
  fun k => (E k).map π.symm.toEmbedding

theorem mem_reindex {m n : ℕ} {π : Equiv.Perm (Fin (n + 1))}
    {E : Fin m → Finset (Fin (n + 1))} {k : Fin m} {j : Fin (n + 1)} :
    j ∈ reindex π E k ↔ π j ∈ E k := by
  simp [reindex, Finset.mem_map_equiv]

/-- Reindexing along the identity changes nothing. -/
@[simp] theorem reindex_refl {m n : ℕ}
    (E : Fin m → Finset (Fin (n + 1))) :
    reindex (Equiv.refl _) E = E := by
  funext k
  ext j
  rw [mem_reindex, Equiv.refl_apply]

/-- **A complete elimination listing, reversed, is a
running-intersection order.**  Placing the last-eliminated vertex
first (`π i` = the vertex at position `n - i` of the listing) makes
every closed canonical separator of the reindexed hypergraph land in
the listing's edge: the earlier neighbours of a vertex are exactly its
not-yet-eliminated neighbours at its elimination step. -/
theorem sepInEdge_of_elimList {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} {L : List (Fin (n + 1))}
    (hL : ElimList E L) (hnd : L.Nodup)
    (hall : ∀ x : Fin (n + 1), x ∈ L) :
    ∃ π : Equiv.Perm (Fin (n + 1)), SepInEdge (reindex π E) := by
  have hlen : L.length = n + 1 := by
    have h1 : L.toFinset = Finset.univ :=
      Finset.eq_univ_of_forall fun x => List.mem_toFinset.mpr (hall x)
    have h2 := List.toFinset_card_of_nodup hnd
    rw [h1, Finset.card_univ, Fintype.card_fin] at h2
    omega
  set f : Fin (n + 1) → Fin (n + 1) := fun i =>
    L.get ⟨n - i.val, by omega⟩ with hf
  have hinj : Function.Injective f := by
    intro i j hij
    have hg := List.nodup_iff_injective_get.mp hnd hij
    have hval : n - i.val = n - j.val := congrArg Fin.val hg
    have hi := Fin.is_le i
    have hj := Fin.is_le j
    exact Fin.ext (by omega)
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, rfl⟩
  refine ⟨Equiv.ofBijective f hbij, ?_⟩
  intro i
  have hi := Fin.is_le i
  obtain ⟨k, hk1, hk2⟩ := hL.property (n - i.val) (by omega)
  refine ⟨k, ?_⟩
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact mem_reindex.mpr hk1
  · obtain ⟨hlt, k', hik', hxk'⟩ := (mem_sepOf _).mp hx
    have hxle := Fin.is_le x
    have hxlt : x.val < i.val := Fin.lt_def.mp hlt
    have hb : n - x.val < L.length := by omega
    have hab : n - i.val < n - x.val := by omega
    exact mem_reindex.mpr
      (hk2 (n - x.val) hb hab ⟨k', mem_reindex.mp hik', mem_reindex.mp hxk'⟩)

/-- **α-acyclicity ⇒ running-intersection order** — the first link of
the BFMY chain, mechanized: a GYO-reducible hypergraph admits a vertex
order (a permutation of the ambient order) along which elimination
creates no fill-in, i.e. `SepInEdge` holds for the reindexed family.
The domination invariant holds trivially at the initial state (every
edge dominates itself). -/
theorem gyoReducible_sepInEdge {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} (h : GYOReducible E) :
    ∃ π : Equiv.Perm (Fin (n + 1)), SepInEdge (reindex π E) := by
  obtain ⟨L, hL, hnd, hmem⟩ :=
    gyo_elimList h fun k => ⟨k, Finset.mem_univ k, subset_rfl⟩
  exact sepInEdge_of_elimList hL hnd
    fun x => (hmem x).mpr (Finset.mem_univ x)

/-! ### Pairwise consistency solves acyclic instances

The second link of the BFMY chain.  "Pairwise consistency ⇒
`EdgeConsistent`" is false in general — `EdgeConsistent` demands
repair of *arbitrary* assignments, which no amount of semijoin
processing provides.  The true theorem is proved instead: on a
hypergraph with the running-intersection property, pairwise-consistent
(semijoin-reduced) nonempty relations admit a global solution.  The
proof is the textbook greedy sweep along the elimination order, with
the invariant that the assigned prefix of every edge extends to a full
tuple of that edge, propagated through the cover edge that `SepInEdge`
provides at each vertex. -/

/-- **Pairwise consistency** (the output condition of a full semijoin
reduction, `beeri1983acyclic`): every domain-respecting tuple of each
relation matches some domain-respecting tuple of every other relation
on their shared attributes. -/
def PairwiseConsistent {m n : ℕ} (D : Fin (n + 1) → Set α)
    (E : Fin m → Finset (Fin (n + 1)))
    (Rel : Fin m → (Fin (n + 1) → α) → Prop) : Prop :=
  ∀ k k' : Fin m, ∀ g : Fin (n + 1) → α, (∀ u, g u ∈ D u) → Rel k g →
    ∃ g', (∀ u, g' u ∈ D u) ∧ Rel k' g' ∧ ∀ u ∈ E k ∩ E k', g' u = g u

/-- **The BFMY solvability theorem, running-intersection form.**  On a
hypergraph whose ambient order has the running-intersection property
(`SepInEdge`), pairwise-consistent nonempty edge relations admit a
global solution.  Greedy sweep with invariant: after assigning
vertices `< i`, the assignment agrees below `i` with a full tuple of
*every* edge.  At vertex `i`, the cover edge `k*` of
`insert i (sepOf E i)` donates its tuple's value at `i`; any edge `k`
containing `i` has all its assigned vertices inside `E k*` (they are
earlier neighbours of `i`), so pairwise consistency between `k*` and
`k` re-supplies a matching tuple of `k`.  Edges not containing `i`
keep their tuples. -/
theorem pairwiseConsistent_solvable {m n : ℕ} {D : Fin (n + 1) → Set α}
    {E : Fin m → Finset (Fin (n + 1))}
    {Rel : Fin m → (Fin (n + 1) → α) → Prop}
    (hsupp : EdgeSupported E Rel) (hRIP : SepInEdge E)
    (hpc : PairwiseConsistent D E Rel)
    (hloc : ∀ k, ∃ t, (∀ u, t u ∈ D u) ∧ Rel k t)
    (hne : ∀ u, (D u).Nonempty) :
    ∃ f : Fin (n + 1) → α, (∀ u, f u ∈ D u) ∧ ∀ k, Rel k f := by
  have key : ∀ i : ℕ, i ≤ n + 1 → ∃ g : Fin (n + 1) → α,
      (∀ u, g u ∈ D u) ∧
      ∀ k, ∃ t, (∀ u, t u ∈ D u) ∧ Rel k t ∧
        ∀ u ∈ E k, u.val < i → t u = g u := by
    intro i
    induction i with
    | zero =>
        intro _
        refine ⟨fun u => (hne u).some, fun u => (hne u).some_mem,
          fun k => ?_⟩
        obtain ⟨t, htD, htR⟩ := hloc k
        exact ⟨t, htD, htR, fun u _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ i ih =>
        intro hi
        obtain ⟨g, hgD, hg⟩ := ih (by omega)
        have hiv : i < n + 1 := by omega
        set v : Fin (n + 1) := ⟨i, hiv⟩ with hv
        obtain ⟨ks, hks⟩ := hRIP v
        obtain ⟨ts, htsD, htsR, htsa⟩ := hg ks
        refine ⟨Function.update g v (ts v), ?_, ?_⟩
        · intro u
          rcases eq_or_ne u v with rfl | hu
          · rw [Function.update_self]
            exact htsD v
          · rw [Function.update_of_ne hu]
            exact hgD u
        · intro k
          by_cases hvk : v ∈ E k
          · obtain ⟨t', ht'D, ht'R, ht'a⟩ := hpc ks k ts htsD htsR
            refine ⟨t', ht'D, ht'R, ?_⟩
            intro u hu hui
            rcases eq_or_ne u v with rfl | hune
            · rw [Function.update_self]
              exact ht'a v (Finset.mem_inter.mpr
                ⟨hks (Finset.mem_insert_self _ _), hvk⟩)
            · have huval : u.val < i := by
                have hne' : u.val ≠ i := fun h => hune (Fin.ext h)
                omega
              have husep : u ∈ sepOf E v := (mem_sepOf E).mpr
                ⟨Fin.lt_def.mpr huval, k, hvk, hu⟩
              have huks : u ∈ E ks := hks (Finset.mem_insert_of_mem husep)
              rw [Function.update_of_ne hune,
                ht'a u (Finset.mem_inter.mpr ⟨huks, hu⟩),
                htsa u huks huval]
          · obtain ⟨t, htD, htR, hta⟩ := hg k
            refine ⟨t, htD, htR, ?_⟩
            intro u hu hui
            have hune : u ≠ v := fun h => hvk (h ▸ hu)
            have huval : u.val < i := by
              have hne' : u.val ≠ i := fun h => hune (Fin.ext h)
              omega
            rw [Function.update_of_ne hune]
            exact hta u hu huval
  obtain ⟨g, hgD, hg⟩ := key (n + 1) le_rfl
  refine ⟨g, hgD, fun k => ?_⟩
  obtain ⟨t, htD, htR, hta⟩ := hg k
  exact (hsupp k t g fun u hu => hta u hu u.isLt).mp htR

/-! ### The headline: the BFMY theorem, fully composed -/

/-- **The Beeri–Fagin–Maier–Yannakakis theorem, mechanized end to
end**: on a GYO-reducible (α-acyclic) hypergraph, pairwise-consistent
(semijoin-reduced) nonempty edge relations admit a global solution.
The acyclicity hypothesis is the GYO reduction itself, the consistency
hypothesis is the honest output condition of a semijoin pass, and no
top-injectivity or per-vertex extendability is assumed.  Proof:
`gyoReducible_sepInEdge` produces a running-intersection reordering
`π`; the instance is transported along `π` (domains, relations and
scopes reindexed), solved by `pairwiseConsistent_solvable`, and the
solution is transported back. -/
theorem gyoReducible_pairwiseConsistent_solvable {m n : ℕ}
    {D : Fin (n + 1) → Set α} {E : Fin m → Finset (Fin (n + 1))}
    {Rel : Fin m → (Fin (n + 1) → α) → Prop}
    (hgyo : GYOReducible E) (hsupp : EdgeSupported E Rel)
    (hpc : PairwiseConsistent D E Rel)
    (hloc : ∀ k, ∃ t, (∀ u, t u ∈ D u) ∧ Rel k t)
    (hne : ∀ u, (D u).Nonempty) :
    ∃ f : Fin (n + 1) → α, (∀ u, f u ∈ D u) ∧ ∀ k, Rel k f := by
  obtain ⟨π, hSIE⟩ := gyoReducible_sepInEdge hgyo
  have hsupp' : EdgeSupported (reindex π E)
      (fun k g => Rel k fun w => g (π.symm w)) := by
    intro k g g' hagree
    exact hsupp k _ _ fun u hu =>
      hagree (π.symm u) (mem_reindex.mpr (by rwa [Equiv.apply_symm_apply]))
  have hpc' : PairwiseConsistent (fun u => D (π u)) (reindex π E)
      (fun k g => Rel k fun w => g (π.symm w)) := by
    intro k k' g hgD hgR
    obtain ⟨h, hhD, hhR, hha⟩ := hpc k k' (fun w => g (π.symm w))
      (fun u => by simpa using hgD (π.symm u)) hgR
    refine ⟨fun w => h (π w), fun u => hhD (π u), ?_, ?_⟩
    · show Rel k' fun w => h (π (π.symm w))
      simpa using hhR
    · intro u hu
      have hu' : π u ∈ E k ∩ E k' := by
        rw [Finset.mem_inter] at hu ⊢
        exact ⟨mem_reindex.mp hu.1, mem_reindex.mp hu.2⟩
      simpa using hha (π u) hu'
  have hloc' : ∀ k, ∃ t : Fin (n + 1) → α,
      (∀ u, t u ∈ D (π u)) ∧ Rel k fun w => t (π.symm w) := by
    intro k
    obtain ⟨t, htD, htR⟩ := hloc k
    refine ⟨fun w => t (π w), fun u => htD (π u), ?_⟩
    show Rel k fun w => t (π (π.symm w))
    simpa using htR
  obtain ⟨f, hfD, hfR⟩ := pairwiseConsistent_solvable hsupp' hSIE hpc'
    hloc' fun u => hne (π u)
  refine ⟨fun w => f (π.symm w), fun u => ?_, fun k => hfR k⟩
  simpa using hfD (π.symm u)

end STE
