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

**Honest boundary.**  Three links of the full BFMY chain are *not*
mechanized here and are not claimed:

1. **α-acyclicity ⇒ `SepInEdge`.**  We take the running-intersection
   consequence `SepInEdge` as the hypothesis rather than deriving it
   from GYO/Graham reduction or from join-tree existence.  Defining
   GYO reduction as a well-founded recursion and proving
   "GYO-reducible ⇒ some vertex order has `SepInEdge`" is the next
   step; it is pure finite combinatorics, independent of everything
   proved here.
2. **Pairwise consistency ⇒ `EdgeConsistent`.**  BFMY's hypothesis is
   that the relations are pairwise consistent (every tuple of one
   relation matches a tuple of each other on shared attributes); the
   join tree then propagates this to extendability at each vertex.  We
   assume extendability (`EdgeConsistent`) directly — it is the output
   condition of the semijoin program, exactly as
   `DirectionalConsistent` is the output condition of bucket
   elimination in `Ste.AdaptiveConsistency`.
3. **One bucket per vertex.**  `edgeConsistent_solvable` assumes
   `top` injective, so each vertex is the last vertex of at most one
   hyperedge and its bucket is a single edge relation.  Without it the
   bucket is a conjunction of several edge relations and
   `EdgeConsistent` would have to be stated for the conjunction — a
   packaging change, not new mathematics, but not done here.

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

end STE
