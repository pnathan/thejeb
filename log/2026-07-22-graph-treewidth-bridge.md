# 2026-07-22 — The graph-treewidth bridge, machine-checked

## Question

> Elimination-induced width = graph tree-decomposition treewidth — we use
> Dechter's induced width (defined via orders); proving it equals the
> tree-decomposition invariant is unformalized. prove it. or disprove it.
> also check bounds. is it Lte or gte?

## Finding (answer first)

It depends on which "induced width" you name, and there is a deliberate
off-by-one in our formalization:

- **Classically** Dechter's induced width and Robertson–Seymour treewidth
  are **equal**: `iw(G) = tw(G)` (Bodlaender; Dechter, *Constraint
  Processing* 2003). Per a *fixed* order it is **GTE**:
  `induced-width(order) ≥ tw(G)`, with equality at the optimal order.
- **Our Lean `inducedTreewidth`** is not Dechter's `iw` — it is `iw − 1`.
  The recorded bag in `bucketHead` is the *message scope* `β(v)` (the
  neighbours of `v`, with `v` itself erased). So `|β(v)| = #neighbours(v)`
  = Dechter's induced width contribution = classical `tw` in the optimal
  order, and `inducedTreewidth B = max_v |β(v)| − 1 = tw(G_B) − 1` for a
  coupled instance.
- The offset is real, not an artifact: a Robertson–Seymour bag must
  include the eliminated vertex `v` (otherwise the edges incident to `v`
  are uncovered), so the elimination bag `{v} ∪ β(v)` is one larger than
  the message scope.

Directionally: `inducedTreewidth B ≤ treewidth(G_B)` (**LTE**), gap
exactly 1. The symbol equal to graph treewidth is `max_v |β(v)|` (largest
message scope), not `inducedTreewidth`.

## What was machine-proven (sorry-free)

New module `lean/Ste/GraphTreewidth.lean` (1000 lines), built from scratch
because Mathlib has `SimpleGraph` but no tree decompositions. CI run #62
green on `research/hyperframes` @ `f103d0f`; merged to `main` @ `f4f22aa`.

- `primalGraph B : SimpleGraph V` — co-occurrence graph; every scope is a
  clique (`isClique_scope`).
- `TreeDecomposition G` — list of bags + strictly increasing parent
  function; the three Robertson–Seymour axioms (`vertexCover`,
  `edgeCover`, `runningIntersection` in parent-closure form, which for an
  increasing parent is equivalent to subtree-connectedness). `width` =
  max bag − 1; `treewidth G := sInf {w | ∃ td, td.width ≤ w}`, nonempty
  and attained via `TreeDecomposition.single`.
- **`primalGraph_elimination_cover`** — some bag list covers every vertex
  and every primal edge, all bags of size ≤ `inducedTreewidth B + 2`
  (the elimination cliques). Unconditional.
- **`treewidth_primalGraph_le`** — `treewidth (primalGraph B) ≤
  inducedTreewidth B + 1`. Proof exhibits a genuine tree decomposition of
  `G_B` — all three axioms, **running intersection included**, discharged
  with no hypothesis and no sorry — via dedup of the optimal order
  (`exists_nodup_order`, empty-scope constraints are `InertLe`), padding
  to eliminate all variables (`padOrder`, padding bags are empty), and a
  recursive construction (`exists_elim_treeDecomposition`) with bag
  `{v} ∪ β(v)` and parent = a later bag containing the message scope.

## What remains outlook

The converse `treewidth(G_B) ≥ inducedTreewidth B + 1` (no tree
decomposition beats elimination) — the deep half, needing a
simplicial-vertex / chordal-completion argument turning any decomposition
into an elimination order of no greater width. Not mechanized.

## Verification discipline

CI run #62 confirmed green independently via GitHub API before merge. Read
the `TreeDecomposition` definition and confirmed the parent-closure
running-intersection formulation is faithful (not vacuous): for a strictly
increasing parent, "every non-topmost occurrence has its parent also
containing `u`" forces the parent-walk to climb through the occurrence set
to its maximum — exactly subtree-connectedness. A chooseable parent only
makes the axiom harder to satisfy, never dodgeable. Full sorry/admit/axiom
sweep clean.

## References

- R. Dechter, *Constraint Processing*, 2003 (induced width, bucket
  elimination).
- N. Robertson, P. D. Seymour, *Graph Minors II* (tree decompositions,
  treewidth).
- H. L. Bodlaender, *A partial k-arboretum of graphs with bounded
  treewidth* (elimination orders and treewidth).
