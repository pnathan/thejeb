/-
The clique lower bound for treewidth, and the exact treewidth of the
`allEqual` coupling's primal graph.

`Ste.GraphTreewidth` proves `treewidth_le_card`, a treewidth UPPER bound
(`treewidth G ≤ Fintype.card V - 1`), but the library had no matching
LOWER bound from clique size.  `papers/papers/ste-cohomology.tex`,
Observation~\ref{obs:arity} ("gluing width must not be confused with
treewidth ... vanishing is not tractability; gluing halves mechanized,
treewidth half a marked sketch") states the gap explicitly: `allEqual`'s
primal graph is complete and its induced width is "maximal (`n-1`)", but
that "half remains a prose observation ... deliberately unmechanized:
the library currently has only a treewidth upper bound
(`treewidth_le_card`, in `Ste.GraphTreewidth`), and no clique lower
bound to cite."  The paper's "What remains conjectural" section repeats
this as the outstanding item: "The treewidth half of the
arity-vs-treewidth separation --- that `allEqual`'s primal-graph induced
width is `n - 1` as a Lean theorem (only the gluing-width-1 half is
mechanized, Observation~\ref{obs:arity})".  This file discharges exactly
that gap.  (The paper's "`n - 1`" is the *classical* induced width; the
repo's `inducedTreewidth` is one less, so what is proved below is
`inducedTreewidth = n - 2`, i.e. `inducedTreewidth + 1 = n - 1`.  See
the convention recorded at `AchievesWidth` in `Ste.Treedecomp`.)

**Contents.**

* `TreeDecomposition.exists_bag_of_isClique`: every clique of a graph
  fits inside a single bag of any of its tree decompositions — take the
  vertex of the clique with the least `TreeDecomposition.top` (from
  `Ste.TreewidthConverse`); every other clique vertex shares a bag with
  it (`edgeCover`), so the chain lemma `mem_top_of_shared_bag` places it
  in the topmost bag of the minimizer.
* `le_treewidth_of_isClique`: **the clique lower bound** — a clique of
  size `s.card` forces `treewidth G ≥ s.card - 1`, since some bag of an
  optimal decomposition contains the whole clique.
* `treewidth_top`: the treewidth of the complete graph on `V` is exactly
  `Fintype.card V - 1` — `treewidth_le_card` for `≤`, the clique bound
  applied to `Finset.univ` for `≥`.
* `allEqualInstance`, `mem_allEqualInstance`, `allEqualInstance_hasSupport`,
  `iInter_allEqualInstance`: the pairwise-equality bucket-list instance of
  `allEqual n α` (one scope `{i, j}` per ordered pair, each holding
  `pairEqConstraint i j` from `Ste.GluingWidth`) — a faithful bucket-list
  presentation, matching the family that already witnesses gluing width 1.
* `primalGraph_allEqualInstance`: the primal graph of that instance is
  the complete graph `⊤` on `Fin n` — every pair of distinct coordinates
  co-occurs in some scope.
* `treewidth_primalGraph_allEqualInstance`: **the headline** —
  `treewidth (primalGraph (allEqualInstance n α)) = n - 1`.  Combined
  with `allEqual_gluesAtWidth_one` (`Ste.GluingWidth`), the
  arity-vs-treewidth separation of Observation~\ref{obs:arity} is now
  two-sided in Lean: gluing width `1` versus treewidth `n - 1`.
* `inducedTreewidth_allEqualInstance`: the same statement in
  bucket-elimination form, via `treewidth_primalGraph_eq`
  (`Ste.TreewidthConverse`): `inducedTreewidth (allEqualInstance n α) + 1
  = n - 1`.

**Width convention.**  The paper's target is stated with the classical
induced width, `n - 1`.  This library's `inducedTreewidth` is one *less*
than the classical induced width (see the convention recorded at
`AchievesWidth` in `Ste.Treedecomp`: bags exclude the eliminated
variable, so `treewidth = inducedTreewidth + 1`).  Hence the mechanized
statement is `inducedTreewidth (allEqualInstance n α) = n - 2`, written
here as `inducedTreewidth ... + 1 = n - 1`; it is the same claim as the
paper's, in the repo's offset.

References: N. Robertson, P. D. Seymour, *Graph minors II* (tree
decompositions, treewidth); H. L. Bodlaender, *A partial k-arboretum of
graphs with bounded treewidth*, Theor. Comput. Sci. 209 (1998) (clique
lower bound on treewidth — every clique fits in a common bag); R.
Dechter, *Constraint Processing*, Morgan Kaufmann, 2003 (bucket
elimination, induced width).
-/
import Ste.TreewidthConverse
import Ste.GluingWidth

namespace STE

open Set

/-! ### List and foldr helpers

These restate the identically-named `private` helpers of
`Ste.TreewidthConverse` (private declarations do not cross file
boundaries), needed here for the same bookkeeping. -/

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

/-! ### The clique lower bound -/

/-- **Every clique of `G` fits inside a single bag** of any tree
decomposition of `G`.  Take the clique vertex `u₀` minimizing
`td.top` over the (nonempty) clique `s`.  It sits in the bag at
position `td.top u₀` (`top_spec`).  Any other clique vertex `v` is
adjacent to `u₀`, hence shares a bag with it (`edgeCover`); minimality
of `td.top u₀` over `s` gives `td.top u₀ ≤ td.top v`, so the chain
lemma `mem_top_of_shared_bag` places `v` in that same bag. -/
theorem TreeDecomposition.exists_bag_of_isClique {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} (td : TreeDecomposition G) {s : Finset V}
    (hs : G.IsClique (s : Set V)) (hne : s.Nonempty) :
    ∃ i, i < td.bags.length ∧ ∀ v ∈ s, v ∈ td.bags.getD i ∅ := by
  obtain ⟨u₀, hu₀s, hu₀min⟩ := Finset.exists_min_image s td.top hne
  refine ⟨td.top u₀, (td.top_spec u₀).1, ?_⟩
  intro v hvs
  by_cases hvu : v = u₀
  · rw [hvu]
    exact (td.top_spec u₀).2
  · have hadj : G.Adj u₀ v :=
      (SimpleGraph.isClique_iff G).mp hs hu₀s hvs (Ne.symm hvu)
    obtain ⟨b, hb, hu₀b, hvb⟩ := td.edgeCover hadj
    obtain ⟨j, hjlen, hjeq⟩ := exists_getD_eq_of_mem (∅ : Finset V) hb
    have hu₀j : u₀ ∈ td.bags.getD j ∅ := hjeq ▸ hu₀b
    have hvj : v ∈ td.bags.getD j ∅ := hjeq ▸ hvb
    have hle : td.top u₀ ≤ td.top v := hu₀min v hvs
    exact td.mem_top_of_shared_bag hjlen hu₀j hvj hle

/-- **The clique lower bound on treewidth.**  A clique of size
`s.card` forces `treewidth G ≥ s.card - 1`: take an optimal tree
decomposition (`exists_treeDecomposition_width_le_treewidth`); some bag
contains the whole clique (`exists_bag_of_isClique`), so its size is at
least `s.card`; every bag's size is bounded by the decomposition's
width plus one. -/
theorem le_treewidth_of_isClique {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {s : Finset V} (hs : G.IsClique (s : Set V)) :
    (s.card - 1 : ℕ) ≤ treewidth G := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨td, htd⟩ := exists_treeDecomposition_width_le_treewidth G
  obtain ⟨i, hilen, hisub⟩ := td.exists_bag_of_isClique hs hne
  have hsub : s ⊆ td.bags.getD i ∅ := hisub
  have hcard : s.card ≤ (td.bags.getD i ∅).card := Finset.card_le_card hsub
  have hmem : td.bags.getD i ∅ ∈ td.bags := getD_mem_of_lt hilen
  have hle : (td.bags.getD i ∅).card ≤ (td.bags.map Finset.card).foldr max 0 :=
    le_foldr_max (List.mem_map.mpr ⟨td.bags.getD i ∅, hmem, rfl⟩)
  have hwidth : (td.bags.map Finset.card).foldr max 0 - 1 ≤ treewidth G := htd
  omega

/-- **The treewidth of the complete graph** on a finite vertex set is
exactly `Fintype.card V - 1`: `treewidth_le_card` for `≤`, and the
clique lower bound applied to `Finset.univ` (a clique of `⊤` since all
distinct vertices are adjacent, `SimpleGraph.top_adj`) for `≥`. -/
theorem treewidth_top {V : Type*} [Fintype V] [DecidableEq V] :
    treewidth (⊤ : SimpleGraph V) = Fintype.card V - 1 := by
  refine le_antisymm (treewidth_le_card ⊤) ?_
  have hclique : (⊤ : SimpleGraph V).IsClique ((Finset.univ : Finset V) : Set V) := by
    rw [SimpleGraph.isClique_iff]
    intro u _ v _ huv
    exact (SimpleGraph.top_adj u v).mpr huv
  have h := le_treewidth_of_isClique hclique
  rwa [Finset.card_univ] at h

/-! ### The pairwise-equality bucket-list instance of `allEqual` -/

/-- **The pairwise-equality bucket-list instance** of `allEqual n α`:
one scope `{i, j}` per ordered pair of coordinates, each holding the
pairwise-equality constraint `pairEqConstraint i j`
(`Ste.GluingWidth`) — the same family that already witnesses
`allEqual_gluesAtWidth_one`, packaged as a `Ste.Treedecomp`
bucket-list instance. -/
def allEqualInstance (n : ℕ) (α : Type*) :
    List (Finset (Fin n) × Set (Fin n → α)) :=
  (List.finRange n).flatMap fun i =>
    (List.finRange n).map fun j => (({i, j} : Finset (Fin n)), pairEqConstraint i j)

/-- Membership in `allEqualInstance`: every entry is `({i, j},
pairEqConstraint i j)` for some pair `i, j`. -/
theorem mem_allEqualInstance {n : ℕ} {α : Type*}
    {q : Finset (Fin n) × Set (Fin n → α)} :
    q ∈ allEqualInstance n α ↔
      ∃ i j : Fin n, q = (({i, j} : Finset (Fin n)), pairEqConstraint i j) := by
  simp only [allEqualInstance, List.mem_flatMap, List.mem_map, List.mem_finRange,
    true_and]
  constructor
  · rintro ⟨i, j, hq⟩
    exact ⟨i, j, hq.symm⟩
  · rintro ⟨i, j, hq⟩
    exact ⟨i, j, hq.symm⟩

/-- **Every scope of `allEqualInstance` is a genuine support** of its
constraint: `{i, j}` supports `pairEqConstraint i j`
(`hasSupport_pairEqConstraint`), read through the `Finset` coercion. -/
theorem allEqualInstance_hasSupport {n : ℕ} {α : Type*} :
    ∀ q ∈ allEqualInstance n α,
      HasSupport (A := fun _ : Fin n => α) q.2 (↑q.1 : Set (Fin n)) := by
  intro q hq
  obtain ⟨i, j, rfl⟩ := mem_allEqualInstance.mp hq
  simpa using hasSupport_pairEqConstraint i j

/-- **Semantic faithfulness**: the intersection of `allEqualInstance`'s
constraints is exactly `allEqual n α`. -/
theorem iInter_allEqualInstance {n : ℕ} {α : Type*} :
    ⋂ q ∈ allEqualInstance n α, q.2 = allEqual n α := by
  ext f
  simp only [Set.mem_iInter, allEqual, Set.mem_setOf_eq]
  constructor
  · intro h i j
    have hmem : (({i, j} : Finset (Fin n)), pairEqConstraint i j) ∈ allEqualInstance n α :=
      mem_allEqualInstance.mpr ⟨i, j, rfl⟩
    exact h _ hmem
  · intro h q hq
    obtain ⟨i, j, rfl⟩ := mem_allEqualInstance.mp hq
    exact h i j

/-! ### The primal graph of `allEqualInstance` is complete -/

/-- **The primal graph of `allEqualInstance n α` is the complete graph**
on `Fin n`: every distinct pair of coordinates co-occurs in the scope
`{i, j}` of `allEqualInstance`. -/
theorem primalGraph_allEqualInstance (n : ℕ) (α : Type*) :
    primalGraph (A := fun _ : Fin n => α) (allEqualInstance n α) = ⊤ := by
  ext u v
  rw [primalGraph_adj, SimpleGraph.top_adj]
  constructor
  · exact fun h => h.1
  · intro huv
    refine ⟨huv, (({u, v} : Finset (Fin n)), pairEqConstraint u v),
      mem_allEqualInstance.mpr ⟨u, v, rfl⟩, ?_, ?_⟩
    · exact Finset.mem_insert_self u {v}
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self v)

/-! ### The headline: `treewidth = n - 1` -/

/-- **Headline: the treewidth of the `allEqual` coupling's primal graph
is exactly `n - 1`.**  This discharges the "treewidth half of the
arity-vs-treewidth separation" left open in
`papers/papers/ste-cohomology.tex`, "What remains conjectural"
(Observation~\ref{obs:arity}: "$\mathrm{allEqual}$'s primal-graph
induced width is $n - 1$ as a Lean theorem" — previously only a prose
observation in `Ste.CouplingLowerBound`, since the library had only the
treewidth upper bound `treewidth_le_card` and no clique lower bound).
Combined with `allEqual_gluesAtWidth_one` (`Ste.GluingWidth`) — gluing
width `1` — the arity-vs-treewidth separation of Observation~\ref{obs:arity}
is now mechanized on both sides: for `n ≥ 3`, gluing width `≠`
treewidth, in Lean.  (For `n ≤ 2` the two coincide — `n - 1 ≤ 1` — so
the separation is genuinely an `n ≥ 3` phenomenon.) -/
theorem treewidth_primalGraph_allEqualInstance (n : ℕ) (α : Type*) :
    treewidth (primalGraph (A := fun _ : Fin n => α) (allEqualInstance n α))
      = n - 1 := by
  rw [primalGraph_allEqualInstance, treewidth_top, Fintype.card_fin]

/-- **The same headline in bucket-elimination form.**  Via
`treewidth_primalGraph_eq` (`Ste.TreewidthConverse`), an adjacency
witness in the primal graph converts the treewidth equality into the
induced-width equality
`inducedTreewidth (allEqualInstance n α) + 1 = n - 1`.

Equivalently `inducedTreewidth (allEqualInstance n α) = n - 2`: the repo's
`inducedTreewidth` sits one below the classical induced width `n - 1`
quoted in the paper (convention at `AchievesWidth`, `Ste.Treedecomp`). -/
theorem inducedTreewidth_allEqualInstance {n : ℕ} {α : Type*} [Nonempty α]
    (hn : 2 ≤ n) :
    inducedTreewidth (allEqualInstance n α) + 1 = n - 1 := by
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ (⟨1, by omega⟩ : Fin n) := by
    intro h
    have h0 : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  have hadj : (primalGraph (A := fun _ : Fin n => α) (allEqualInstance n α)).Adj
      (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) := by
    rw [primalGraph_allEqualInstance]
    exact (SimpleGraph.top_adj _ _).mpr h01
  rw [← treewidth_primalGraph_eq (allEqualInstance n α) hadj,
    treewidth_primalGraph_allEqualInstance]

end STE
