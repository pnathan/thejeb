/-
Join trees ⟺ GYO reducibility: the equivalence of the two classical
definitions of α-acyclicity, mechanized.

`Ste.AcyclicSolvability` mechanizes GYO (Graham / Yu–Ozsoyoglu)
reduction as the inductive predicate `GYO` and proves the BFMY
solvability pipeline from `GYOReducible`.  Its honest-residue note
left one boundary item open: the equivalence of GYO reducibility with
the OTHER standard definitions of α-acyclicity.  This file closes the
join-tree half of that item:

* `JoinTree E` — a **join tree** for the hyperedge family
  `E : Fin m → Finset (Fin (n + 1))`.  Encoding (chosen for
  mechanizability, in the house parent-function style of
  `Ste.ConsistencyTree`): a permutation `ord` listing the edges
  (position `a` carries edge `E (ord a)`), a parent map `par` on
  positions with root at position `0` and every non-root position's
  parent strictly earlier (`par_lt` — the decreasing-to-root
  wellfoundedness), and the **ordered running-intersection property**
  `rip`: a vertex shared by the edge at position `a` and ANY earlier
  edge belongs to the parent edge of `a`.  This is the classical
  "running intersection ordering" form of the join-tree / junction
  property: for a rooted join tree listed in any DFS (parent-first)
  order, a vertex shared with an earlier edge is shared with an edge
  outside the subtree of `a`, and the tree path to it passes through
  `par a`, so the junction property (the set of tree nodes containing
  each vertex is connected) yields exactly `rip`; conversely `rip`
  makes the parent-chain from any node descend through nodes
  containing the shared vertex, which is the junction property along
  ancestor paths (`JoinTree.mem_par` is the one-step form).  Only the
  `rip` form is mechanized; the reformulation as connectivity of
  tree PATHS between arbitrary pairs of nodes is classical bookkeeping
  (least-position-containing-`v` arguments) and is not formalized.
  `cover` (every vertex lies in some edge) is included because `GYO`'s
  ear rule demands it — see honest-residue note (2) of
  `Ste.AcyclicSolvability` — so it is forced on both sides of the
  equivalence.

* `joinTree_gyoReducible : JoinTree E → GYOReducible E` — the
  classical leaf-plucking direction.  Processing positions from the
  last to the first: the private vertices of the last live edge (those
  in no earlier edge) are ears; after removing them the edge's live
  part is contained in its parent edge by `rip`, so the edge
  contracts.  Mechanized as one induction on the number of live
  positions (`gyo_of_ears` handles the ear batch).

* `gyoReducible_joinTree : GYOReducible E → Nonempty (JoinTree E)` —
  the converse, built along the GYO run.  `gyo_ripList` extracts from
  a `GYO` derivation a listing of the live edges (contracted edges
  first, in contraction order, then the never-contracted survivors)
  with the positional property "each non-final position has a later
  *dominator* position absorbing its intersection with every later
  edge, on the live vertices": an ear step preserves the property
  (the eared vertex lies in exactly one live edge, so it never
  witnesses a shared pair), and a contract step prepends the removed
  edge with its dominator as parent.  Reversing the listing (so
  parents come first) gives the `JoinTree`; `gyo_cover` supplies
  `cover`.

* `joinTree_iff_gyoReducible` — the packaged equivalence
  `Nonempty (JoinTree E) ↔ GYOReducible E`.

* `joinTree_pairwiseConsistent_solvable` — the composed corollary:
  a join tree plus edge-scoped (`EdgeSupported`), pairwise-consistent
  (`PairwiseConsistent`), nonempty local relations yield a global
  solution, via the equivalence and
  `gyoReducible_pairwiseConsistent_solvable`.

**Relation to `Ste.JunctionTree`.**  The junction-tree representation
of that file lives on the OUTPUT of a bucket-elimination run (bags of
an elimination order, with size bounds); the `JoinTree` here is the
input-side combinatorial object on the hyperedges themselves.  The
bucket bags of a width-bounded run form a join tree in the present
sense (bags ordered by elimination step, each bag's parent the bag
where its residual separator lands) — that connection is a remark
only; no code dependency in either direction.

**What is mechanized, and what is not.**  Mechanized, sorry-free:
join-tree existence ⟺ GYO-reducibility (both directions, for
hypergraphs on the vertex set `Fin (n + 1)` with every vertex covered
— coverage being forced by `GYO`'s ear rule).  Together with
`gyoReducible_sepInEdge` of `Ste.AcyclicSolvability` this mechanizes
the equivalence of three of the classical characterizations of
α-acyclicity: join tree ⟺ GYO ⟺ (one direction) running-intersection
order.  NOT mechanized: the remaining classical characterizations —
conformal + chordal primal graph, and Bachman-diagram forms — remain
outside scope, as does the tree-PATH phrasing of the junction
property (see the `JoinTree` docstring).

References: C. Beeri, R. Fagin, D. Maier, M. Yannakakis, *On the
desirability of acyclic database schemes*, JACM 30(3):479–513, 1983
(`beeri1983acyclic`; Theorem 3.4 there is the join-tree ⟺ GYO ⟺
α-acyclic equivalence); M. H. Graham, *On the universal relation*,
Univ. of Toronto TR, 1979, and C. T. Yu, M. Z. Ozsoyoglu, *An
algorithm for tree-query membership of a distributed query*,
COMPSAC 1979 (the GYO reduction); R. Dechter, *Constraint
Processing*, 2003, ch. 4.
-/
import Ste.AcyclicSolvability

namespace STE

variable {α : Type*}

/-! ### Join trees -/

/-- **A join tree** for the hyperedge family `E`: a rooted tree on
edge positions.  `ord` is a listing of the edges (position `a` carries
edge `E (ord a)`), `par` the parent map on positions with the root at
position `0` and parents strictly earlier (`par_lt`), and `rip` the
ordered running-intersection / junction property: a vertex shared by
the edge at position `a` and any EARLIER edge lies in the parent edge
of `a`.  `cover` (every vertex in some edge) is forced by the ear rule
of `GYO` (honest-residue note (2) of `Ste.AcyclicSolvability`).  See
the module docstring for why this ordered form is the junction
property and for what is not mechanized. -/
structure JoinTree {m n : ℕ} (E : Fin m → Finset (Fin (n + 1))) where
  /-- The edge listed at each tree position. -/
  ord : Equiv.Perm (Fin m)
  /-- The parent position of each position (root: position `0`). -/
  par : Fin m → Fin m
  /-- Parents are strictly earlier: the tree is rooted at position
  `0` and decreasing to the root. -/
  par_lt : ∀ a : Fin m, 0 < a.val → (par a).val < a.val
  /-- The running-intersection / junction property, ordered form: a
  vertex shared with any earlier edge lies in the parent edge. -/
  rip : ∀ a b : Fin m, b.val < a.val → ∀ v : Fin (n + 1),
    v ∈ E (ord a) → v ∈ E (ord b) → v ∈ E (ord (par a))
  /-- Every vertex lies in some hyperedge. -/
  cover : ∀ v : Fin (n + 1), ∃ k, v ∈ E k

/-- One-step junction property along ancestor chains: a vertex shared
between two tree nodes belongs to the parent of the later one — so,
iterating (`par_lt` makes positions strictly descend), the
parent-chain of any node passes only through nodes containing the
shared vertex, which is the junction property along ancestor paths. -/
theorem JoinTree.mem_par {m n : ℕ} {E : Fin m → Finset (Fin (n + 1))}
    (jt : JoinTree E) {a b : Fin m} (hab : b.val < a.val)
    {v : Fin (n + 1)} (hva : v ∈ E (jt.ord a)) (hvb : v ∈ E (jt.ord b)) :
    v ∈ E (jt.ord (jt.par a)) :=
  jt.rip a b hab v hva hvb

/-! ### Join tree ⇒ GYO: plucking leaves -/

/-- **Batch ear removal.**  If every vertex of `T` lies in exactly one
live edge, then reducing the state with `T` removed reduces the full
state: the vertices of `T` are ears, removable one at a time. -/
theorem gyo_of_ears {m n : ℕ} {E : Fin m → Finset (Fin (n + 1))}
    {K : Finset (Fin m)} (T : Finset (Fin (n + 1))) :
    ∀ S : Finset (Fin (n + 1)),
      (∀ v ∈ T, ∃ k₀ ∈ K, v ∈ E k₀ ∧ ∀ k ∈ K, v ∈ E k → k = k₀) →
      GYO E (S \ T) K → GYO E S K := by
  induction T using Finset.induction_on with
  | empty =>
      intro S _ h
      rwa [Finset.sdiff_empty] at h
  | @insert w T' hw ih =>
      intro S hT h
      have hEq : S.erase w \ T' = S \ insert w T' := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
        tauto
      have h1 : GYO E (S.erase w) K :=
        ih (S.erase w) (fun v hv => hT v (Finset.mem_insert_of_mem hv))
          (by rwa [hEq])
      by_cases hwS : w ∈ S
      · obtain ⟨k₀, hk₀, hwk₀, honly⟩ := hT w (Finset.mem_insert_self _ _)
        exact GYO.ear hwS hk₀ hwk₀ honly h1
      · rwa [Finset.erase_eq_of_notMem hwS] at h1

/-- **Join tree ⇒ GYO-reducible** — the classical leaf-plucking
direction.  Induction on the number `t` of live positions: with live
vertices `⋃_{a < t} E (ord a)` and live edges `{ord a | a < t}`, step
`t + 1 → t` first ear-removes the private vertices of the edge at
position `t` (a vertex of it lying in no earlier edge lies in no other
live edge), after which the edge's live part is contained in its
parent edge by `rip`, so the edge contracts (for `t = 0` the state is
already empty).  At `t = m`, `cover` makes the live vertex set the
full universe. -/
theorem joinTree_gyoReducible {m n : ℕ} {E : Fin m → Finset (Fin (n + 1))}
    (jt : JoinTree E) : GYOReducible E := by
  set St : ℕ → Finset (Fin (n + 1)) := fun t =>
    (Finset.univ.filter (fun a : Fin m => a.val < t)).biUnion
      (fun a => E (jt.ord a)) with hSt
  set Kt : ℕ → Finset (Fin m) := fun t =>
    (Finset.univ.filter (fun a : Fin m => a.val < t)).image jt.ord with hKt
  have hmemS : ∀ t v, v ∈ St t ↔ ∃ a : Fin m, a.val < t ∧ v ∈ E (jt.ord a) := by
    intro t v
    simp [hSt, Finset.mem_biUnion, Finset.mem_filter]
  have hmemK : ∀ t k, k ∈ Kt t ↔ ∃ a : Fin m, a.val < t ∧ jt.ord a = k := by
    intro t k
    simp [hKt, Finset.mem_image, Finset.mem_filter]
  have key : ∀ t : ℕ, GYO E (St t) (Kt t) := by
    intro t
    induction t with
    | zero =>
        have h0 : St 0 = ∅ := by
          ext v
          simp [hmemS]
        rw [h0]
        exact GYO.empty _
    | succ t ih =>
        by_cases ht : t < m
        · set a₀ : Fin m := ⟨t, ht⟩ with ha₀
          set k₀ : Fin m := jt.ord a₀ with hk₀
          have ha₀v : a₀.val = t := by rw [ha₀]
          have hSsucc : ∀ v, v ∈ St (t + 1) ↔ v ∈ St t ∨ v ∈ E k₀ := by
            intro v
            rw [hmemS, hmemS]
            constructor
            · rintro ⟨a, ha, hv⟩
              rcases Nat.lt_or_ge a.val t with h | h
              · exact Or.inl ⟨a, h, hv⟩
              · have haa : a = a₀ := Fin.ext (by omega)
                refine Or.inr ?_
                rw [hk₀, ← haa]
                exact hv
            · rintro (⟨a, ha, hv⟩ | hv)
              · exact ⟨a, by omega, hv⟩
              · exact ⟨a₀, by omega, by rw [← hk₀]; exact hv⟩
          have hk₀K : k₀ ∈ Kt (t + 1) :=
            (hmemK _ _).mpr ⟨a₀, by omega, hk₀.symm⟩
          -- the only live edge containing a private vertex of `k₀` is `k₀`
          have honly : ∀ v, v ∈ E k₀ → v ∉ St t →
              ∀ k ∈ Kt (t + 1), v ∈ E k → k = k₀ := by
            intro v _ hvS k hk hvk
            obtain ⟨b, hb, rfl⟩ := (hmemK _ _).mp hk
            rcases Nat.lt_or_ge b.val t with h | h
            · exact absurd ((hmemS _ _).mpr ⟨b, h, hvk⟩) hvS
            · have hba : b = a₀ := Fin.ext (by omega)
              rw [hba]
          have hsplit : St (t + 1) \ (E k₀ \ St t) = St t := by
            ext v
            simp only [Finset.mem_sdiff]
            constructor
            · rintro ⟨hv1, hv2⟩
              rcases (hSsucc v).mp hv1 with h | h
              · exact h
              · by_contra hvS
                exact hv2 ⟨h, hvS⟩
            · intro hv
              exact ⟨(hSsucc v).mpr (Or.inl hv), fun h => h.2 hv⟩
          refine gyo_of_ears (E k₀ \ St t) (St (t + 1)) ?_ ?_
          · intro v hv
            obtain ⟨hvk₀, hvS⟩ := Finset.mem_sdiff.mp hv
            exact ⟨k₀, hk₀K, hvk₀, honly v hvk₀ hvS⟩
          · rw [hsplit]
            rcases Nat.eq_zero_or_pos t with rfl | htpos
            · have h0 : St 0 = ∅ := by
                ext v
                simp [hmemS]
              rw [h0]
              exact GYO.empty _
            · -- contract the edge at position `t` into its parent
              set k' : Fin m := jt.ord (jt.par a₀) with hk'
              have hpar_lt : (jt.par a₀).val < t := jt.par_lt a₀ htpos
              have hk'K : k' ∈ Kt (t + 1) :=
                (hmemK _ _).mpr ⟨jt.par a₀, by omega, hk'.symm⟩
              have hne : k' ≠ k₀ := by
                intro hcon
                rw [hk', hk₀] at hcon
                have := congrArg Fin.val (jt.ord.injective hcon)
                omega
              have hsub : E k₀ ∩ St t ⊆ E k' ∩ St t := by
                intro v hv
                obtain ⟨hv1, hv2⟩ := Finset.mem_inter.mp hv
                obtain ⟨b, hb, hvb⟩ := (hmemS _ _).mp hv2
                rw [hk₀] at hv1
                refine Finset.mem_inter.mpr ⟨?_, hv2⟩
                rw [hk']
                exact jt.rip a₀ b (by omega) v hv1 hvb
              have hKerase : (Kt (t + 1)).erase k₀ = Kt t := by
                ext k
                rw [Finset.mem_erase, hmemK, hmemK]
                constructor
                · rintro ⟨hkne, b, hb, rfl⟩
                  rcases Nat.lt_or_ge b.val t with h | h
                  · exact ⟨b, h, rfl⟩
                  · exfalso
                    apply hkne
                    have hba : b = a₀ := Fin.ext (by omega)
                    rw [hba]
                · rintro ⟨b, hb, rfl⟩
                  refine ⟨fun hcon => ?_, b, by omega, rfl⟩
                  rw [hk₀] at hcon
                  have := congrArg Fin.val (jt.ord.injective hcon)
                  omega
              exact GYO.contract hk₀K hk'K hne hsub (hKerase ▸ ih)
        · -- `t ≥ m`: the state is unchanged
          have hS : St (t + 1) = St t := by
            ext v
            rw [hmemS, hmemS]
            constructor <;> rintro ⟨a, ha, hv⟩ <;>
              exact ⟨a, by have := a.isLt; omega, hv⟩
          have hK : Kt (t + 1) = Kt t := by
            ext k
            rw [hmemK, hmemK]
            constructor <;> rintro ⟨a, ha, hv⟩ <;>
              exact ⟨a, by have := a.isLt; omega, hv⟩
          rw [hS, hK]
          exact ih
  have hSm : St m = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    obtain ⟨k, hk⟩ := jt.cover v
    exact (hmemS _ _).mpr ⟨jt.ord.symm k, (jt.ord.symm k).isLt,
      by rwa [Equiv.apply_symm_apply]⟩
  have hKm : Kt m = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro k
    exact (hmemK _ _).mpr ⟨jt.ord.symm k, (jt.ord.symm k).isLt,
      Equiv.apply_symm_apply _ _⟩
  have := key m
  rwa [hSm, hKm] at this

/-! ### GYO ⇒ join tree: building the tree along the run -/

/-- **Coverage is forced by GYO**: every live vertex of a reducible
state lies in some hyperedge, because it can only leave the state as
an ear.  At the full state: every vertex lies in some edge. -/
theorem gyo_cover {m n : ℕ} {E : Fin m → Finset (Fin (n + 1))} :
    ∀ {S : Finset (Fin (n + 1))} {K : Finset (Fin m)}, GYO E S K →
      ∀ v ∈ S, ∃ k, v ∈ E k := by
  intro S K h
  induction h with
  | empty K =>
      intro v hv
      exact absurd hv (Finset.notMem_empty v)
  | @ear S K v k₀ hv hk₀ hvk₀ honly h ih =>
      intro u hu
      rcases eq_or_ne u v with rfl | hne
      · exact ⟨k₀, hvk₀⟩
      · exact ih u (Finset.mem_erase.mpr ⟨hne, hu⟩)
  | @contract S K k k' hk hk' hne hsub h ih =>
      exact ih

/-- **The edge listing of a GYO run.**  From a `GYO` derivation,
extract a duplicate-free listing of the live edges — contracted edges
first, in contraction order, then the never-contracted survivors —
with the positional domination property: every non-final position `a`
has a strictly later position `b` (its *dominator*: the contract
step's dominating edge, or, for survivors, arbitrary — survivors
share no live vertex) such that any live vertex shared between the
edge at `a` and the edge at any later position `c` lies in the edge at
`b`.  An ear step preserves the property because the eared vertex lies
in exactly one live edge, so it never witnesses a shared pair of
distinct positions; a contract step prepends the removed edge, with
the dominating edge's position as the witness. -/
theorem gyo_ripList {m n : ℕ} {E : Fin m → Finset (Fin (n + 1))} :
    ∀ {S : Finset (Fin (n + 1))} {K : Finset (Fin m)}, GYO E S K →
      ∃ L : List (Fin m), L.Nodup ∧ (∀ k, k ∈ L ↔ k ∈ K) ∧
        ∀ (a : ℕ) (ha : a + 1 < L.length),
          ∃ b : ℕ, ∃ hb : b < L.length, a < b ∧
            ∀ (c : ℕ) (hc : c < L.length), a < c → ∀ v ∈ S,
              v ∈ E (L.get ⟨a, by omega⟩) → v ∈ E (L.get ⟨c, hc⟩) →
                v ∈ E (L.get ⟨b, hb⟩) := by
  intro S K h
  induction h with
  | empty K =>
      refine ⟨K.toList, K.nodup_toList, fun k => Finset.mem_toList, ?_⟩
      intro a ha
      exact ⟨a + 1, ha, Nat.lt_succ_self a,
        fun c hc hac v hv _ _ => absurd hv (Finset.notMem_empty v)⟩
  | @ear S K v k₀ hv hk₀ hvk₀ honly h ih =>
      obtain ⟨L, hnd, hmem, hP⟩ := ih
      refine ⟨L, hnd, hmem, ?_⟩
      intro a ha
      obtain ⟨b, hb, hab, hcov⟩ := hP a ha
      refine ⟨b, hb, hab, ?_⟩
      intro c hc hac u hu hua huc
      rcases eq_or_ne u v with rfl | hne
      · -- the eared vertex lies in exactly one live edge: contradiction
        have hka : L.get ⟨a, by omega⟩ ∈ K :=
          (hmem _).mp (List.get_mem L ⟨a, by omega⟩)
        have hkc : L.get ⟨c, hc⟩ ∈ K := (hmem _).mp (List.get_mem L ⟨c, hc⟩)
        have h1 : L.get ⟨a, by omega⟩ = k₀ := honly _ hka hua
        have h2 : L.get ⟨c, hc⟩ = k₀ := honly _ hkc huc
        have h3 : (⟨a, by omega⟩ : Fin L.length) = ⟨c, hc⟩ :=
          List.nodup_iff_injective_get.mp hnd (h1.trans h2.symm)
        have hac2 : a = c := congrArg Fin.val h3
        omega
      · exact hcov c hc hac u (Finset.mem_erase.mpr ⟨hne, hu⟩) hua huc
  | @contract S K k k' hk hk' hne hsub h ih =>
      obtain ⟨L, hnd, hmem, hP⟩ := ih
      have hkL : k ∉ L := fun hkl =>
        absurd ((hmem k).mp hkl) (fun hke => (Finset.mem_erase.mp hke).1 rfl)
      refine ⟨k :: L, List.nodup_cons.mpr ⟨hkL, hnd⟩, ?_, ?_⟩
      · intro j
        rw [List.mem_cons, hmem, Finset.mem_erase]
        constructor
        · rintro (rfl | ⟨-, hj⟩)
          exacts [hk, hj]
        · intro hj
          rcases eq_or_ne j k with rfl | hjk
          · exact Or.inl rfl
          · exact Or.inr ⟨hjk, hj⟩
      · intro a ha
        cases a with
        | zero =>
            -- position 0 is the freshly contracted edge; its dominator
            -- `k'` survives into the tail
            have hk'L : k' ∈ L := (hmem k').mpr (Finset.mem_erase.mpr ⟨hne, hk'⟩)
            obtain ⟨b0, hb0, hb0k⟩ := List.mem_iff_getElem.mp hk'L
            refine ⟨b0 + 1, by simpa using Nat.succ_lt_succ hb0,
              Nat.succ_pos b0, ?_⟩
            intro c hc hc0 u hu hua huc
            have hgb : (k :: L).get ⟨b0 + 1, by simpa using Nat.succ_lt_succ hb0⟩
                = k' := by
              simpa [List.get_cons_succ] using hb0k
            have hga : (k :: L).get ⟨0, by omega⟩ = k := rfl
            rw [hga] at hua
            rw [hgb]
            exact (Finset.mem_inter.mp
              (hsub (Finset.mem_inter.mpr ⟨hua, hu⟩))).1
        | succ a =>
            have ha' : a + 1 < L.length := by
              simpa using ha
            obtain ⟨b, hb, hab, hcov⟩ := hP a ha'
            refine ⟨b + 1, by simpa using Nat.succ_lt_succ hb,
              Nat.succ_lt_succ hab, ?_⟩
            intro c hc hac u hu hua huc
            cases c with
            | zero => omega
            | succ c =>
                have hc' : c < L.length := by simpa using hc
                exact hcov c hc' (by omega) u hu hua huc

/-- **GYO-reducible ⇒ join tree.**  The edge listing of the run
(`gyo_ripList`), reversed so that parents precede children, is a join
tree: position `a` carries the edge at listing position `m - 1 - a`,
and the parent of a non-root position is the (earlier) position of its
dominator.  `cover` is `gyo_cover`. -/
theorem gyoReducible_joinTree {m n : ℕ} {E : Fin m → Finset (Fin (n + 1))}
    (h : GYOReducible E) : Nonempty (JoinTree E) := by
  obtain ⟨L, hnd, hmem, hP⟩ := gyo_ripList h
  have hall : ∀ k, k ∈ L := fun k => (hmem k).mpr (Finset.mem_univ k)
  have hlen : L.length = m := by
    have h1 : L.toFinset = Finset.univ :=
      Finset.eq_univ_of_forall fun x => List.mem_toFinset.mpr (hall x)
    have h2 := List.toFinset_card_of_nodup hnd
    rw [h1, Finset.card_univ, Fintype.card_fin] at h2
    omega
  set f : Fin m → Fin m := fun a =>
    L.get ⟨m - 1 - a.val, by have := a.isLt; omega⟩ with hf
  have hinj : Function.Injective f := by
    intro i j hij
    have hg := List.nodup_iff_injective_get.mp hnd hij
    have hval : m - 1 - i.val = m - 1 - j.val := congrArg Fin.val hg
    have hi := i.isLt
    have hj := j.isLt
    exact Fin.ext (by omega)
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, rfl⟩
  -- extract the dominator-position function from the listing property
  choose bfun hblt hbgt hcov using hP
  have hPa : ∀ a : Fin m, 0 < a.val →
      m - 1 - a.val + 1 < L.length := by
    intro a ha
    have := a.isLt
    omega
  set pf : Fin m → Fin m := fun a =>
    if h : 0 < a.val then
      ⟨m - 1 - bfun (m - 1 - a.val) (hPa a h),
        by have := a.isLt; omega⟩
    else a
    with hpf
  refine ⟨⟨Equiv.ofBijective f hbij, pf, ?_, ?_,
    fun v => gyo_cover h v (Finset.mem_univ v)⟩⟩
  · -- `par_lt`
    intro a ha
    have h1 := hblt (m - 1 - a.val) (hPa a ha)
    have h2 := hbgt (m - 1 - a.val) (hPa a ha)
    have h3 := a.isLt
    have hval : (pf a).val = m - 1 - bfun (m - 1 - a.val) (hPa a ha) := by
      simp only [hpf, dif_pos ha]
    rw [hval]
    omega
  · -- `rip`
    intro a b hab v hva hvb
    have ha : 0 < a.val := by omega
    have hia := a.isLt
    have hib := b.isLt
    have hva' : v ∈ E (L.get ⟨m - 1 - a.val, by omega⟩) := hva
    have hvb' : v ∈ E (L.get ⟨m - 1 - b.val, by omega⟩) := hvb
    have hc : m - 1 - b.val < L.length := by omega
    have hac : m - 1 - a.val < m - 1 - b.val := by omega
    have hres := hcov (m - 1 - a.val) (hPa a ha) (m - 1 - b.val) hc hac
      v (Finset.mem_univ v) hva' hvb'
    have hblt' := hblt (m - 1 - a.val) (hPa a ha)
    have hbgt' := hbgt (m - 1 - a.val) (hPa a ha)
    -- the goal is membership in the edge at the dominator's position
    show v ∈ E (f (pf a))
    have hpfa : pf a = ⟨m - 1 - bfun (m - 1 - a.val) (hPa a ha),
        by omega⟩ := by
      simp only [hpf, dif_pos ha]
    rw [hpfa]
    show v ∈ E (L.get ⟨m - 1 - (m - 1 - bfun (m - 1 - a.val) (hPa a ha)),
      by omega⟩)
    have hidx : (⟨m - 1 - (m - 1 - bfun (m - 1 - a.val) (hPa a ha)),
        by omega⟩ : Fin L.length)
        = ⟨bfun (m - 1 - a.val) (hPa a ha), hblt'⟩ := by
      apply Fin.ext
      show m - 1 - (m - 1 - bfun (m - 1 - a.val) (hPa a ha))
        = bfun (m - 1 - a.val) (hPa a ha)
      omega
    rw [hidx]
    exact hres

/-! ### The equivalence, packaged -/

/-- **Join-tree existence ⟺ GYO-reducibility** — the BFMY equivalence
of the two definitions of α-acyclicity (`beeri1983acyclic`,
Thm. 3.4), both directions mechanized. -/
theorem joinTree_iff_gyoReducible {m n : ℕ}
    {E : Fin m → Finset (Fin (n + 1))} :
    Nonempty (JoinTree E) ↔ GYOReducible E :=
  ⟨fun ⟨jt⟩ => joinTree_gyoReducible jt, gyoReducible_joinTree⟩

/-! ### The composed pipeline corollary -/

/-- **Join tree + pairwise consistency ⇒ global solution**: the BFMY
solvability theorem with the acyclicity hypothesis in join-tree form.
Composition of the equivalence (`joinTree_gyoReducible`) with the
headline `gyoReducible_pairwiseConsistent_solvable` of
`Ste.AcyclicSolvability`. -/
theorem joinTree_pairwiseConsistent_solvable {m n : ℕ}
    {D : Fin (n + 1) → Set α} {E : Fin m → Finset (Fin (n + 1))}
    {Rel : Fin m → (Fin (n + 1) → α) → Prop}
    (hjt : JoinTree E) (hsupp : EdgeSupported E Rel)
    (hpc : PairwiseConsistent D E Rel)
    (hloc : ∀ k, ∃ t, (∀ u, t u ∈ D u) ∧ Rel k t)
    (hne : ∀ u, (D u).Nonempty) :
    ∃ f : Fin (n + 1) → α, (∀ u, f u ∈ D u) ∧ ∀ k, Rel k f :=
  gyoReducible_pairwiseConsistent_solvable
    (joinTree_gyoReducible hjt) hsupp hpc hloc hne

end STE
