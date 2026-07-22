# 2026-07-22 — BFS sweep of the tractability frontier

Directive: "keep working through the unformalized bits. work the bfs until
all leads are run down — with us or with accepted peer reviewed papers."

Ran down every open "outlook/conjecture" claim in the tractability program.
Each lead terminates in either a machine proof (sorry-free, CI-green, merged
to main) or a citation to an accepted peer-reviewed result. Six machine-proof
leads were dispatched as parallel `fable` subagents, each isolated in its own
git worktree on a `research/<lead>` branch (CI trigger widened to
`research/**`); I verified every theorem statement independently and merged
each green branch to main.

## Machine-proven (ours), all sorry-free on main

| Lead | Module | Headline theorem |
|---|---|---|
| A | `Ste.TreewidthConverse` | `treewidth_primalGraph_eq`: `tw(G_B) = inducedTreewidth B + 1` — the **full** Robertson–Seymour/Dechter equivalence, both directions (converse via `bucketBags_card_le_of_pairwise_top`, extracting an elimination order from a tree decomposition by ascending topmost-bag position; chain lemma `mem_top_of_shared_bag`). Unconditional `max`-form `max_treewidth_primalGraph_one_eq`. |
| B | `Ste.Projection` | `project_nonempty_iff` + `projectEliminate_decides_feasibility`: projective (∃-)elimination decides **unconditional** feasibility (`= univ ↔ feasible`, `= ∅ ↔ infeasible`), removing the substitution caveat of the conditioning fold. |
| C | `Ste.Factorization` | `encard_feasibilitySet_blocks`: `|feas| = ∏ i, |C i|` over an n-block partition (via `Set.encard_pi_eq_prod_encard`). |
| D | `Ste.VariablePresheaf` | `rectangular_glue` (unique global glue for rectangles) and `diagonal_gluing_fails` (explicit non-gluing local sections); presheaf functoriality `restrict_restrict`. |
| E | `Ste.CechObstruction` | `rectangular_cechObstruction = 0`, `diagonal_cechObstruction = 2 ≠ 0`; `rectangular_of_cechVanishes` bridges to Sheaf rectangularity. Concrete Čech Ȟ¹ for the singleton cover. |
| F | `Ste.JunctionTree` | `junctionTree_size_le` (n·k^(tw+1), faithful bag tables) and `junctionTree_size_linear` (fixed-width O(n)). |

## Closed by peer-reviewed citation

- **Computing tw(B) is NP-hard** → Arnborg–Corneil–Proskurowski 1987
  (`arnborg1987complexity`). Settled hardness, not a gap.
- **Bounded-treewidth CSP tractability / dichotomy** → Freuder 1982
  (`freuder1982backtrack`), Grohe 2007 (`grohe2007complexity`), Dechter 2003.
  The tractable direction is mechanized as lead F; the matching lower bound
  is the classical dichotomy.
- **Elimination width = treewidth (classical)** → Bodlaender 1998
  (`bodlaender1998arboretum`), Robertson–Seymour Graph Minors II
  (`robertson1986graphminorsII`) — now also mechanized as lead A.

## Remaining genuine outlook (honestly flagged)

- The general cohomological programme: the full Čech Ȟ¹ functor over
  arbitrary covers, k-consistency as higher gluing, the quantitative
  "obstruction size = representation blow-up" claim, and the matching
  intractability lower bound (unbounded coupling forces 2^N).
- Efficient computation of treewidth (NP-hard, cited).

## Verification discipline (per "distrust results that aren't machine proven")

- Every agent's file was read for actual theorem statements (not just
  compilation) and swept for `sorry`/`admit`/`axiom`/`native_decide`.
- Every branch's CI run was confirmed green via the GitHub API before merge;
  the fully-integrated main was re-checked.
- **Lead F failed its first CI** (a `Nat.sInf_mem` elaboration type-mismatch,
  not a sorry) despite the agent reporting completion — caught via
  independent CI check, fixed in one line (explicit-set tactic form, same
  pattern as `achievesWidth_inducedTreewidth`), reconfirmed green.
- **Lead A**, flagged going in as likely-outlook, returned the entire hard
  converse; the whole argument was traced by hand before merging.
- Subagents share the working tree via git worktrees; one agent's checkout
  moved the primary branch pointer mid-merge. Recovered with no data loss
  (pushed the affected merge to main by ref) and switched to a dedicated
  integration worktree for all subsequent merges.

## Result

The tractability program is now machine-proven end to end: the feasible set
of a bounded-treewidth STE instance has a faithful polynomial-size
junction-tree representation, feasibility is decided unconditionally by
projective elimination, the induced width is provably the graph treewidth,
independent blocks factor multiplicatively, and the coupling obstruction is
a computed nonzero Čech class. Documented in
`papers/notes/ste-representation-sheaves.tex` (13 pp).
