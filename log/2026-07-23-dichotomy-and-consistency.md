# 2026-07-23 — Closing the queue: dichotomy hard side + Freuder tractability

Directive: "continue working and close all open questions. identify the
problem, solve it, using lean, then anything conjectured or assumed — add it
to the problem-solve queue."

Ran the self-driving solve loop on the frontier left after the BFS sweep.
Two Lean problems solved and merged; the residual is a precisely-stated,
genuinely-open research conjecture, documented rather than faked.

## Q1 — the tractability dichotomy's hard side (`Ste.CouplingLowerBound`)

The junction-tree result (`Ste.JunctionTree`) gave the tractable direction
(bounded width → linear representation). Q1 supplies the matching lower
bound, machine-checked:

- **`cechVanishes_iff_rectangular`** — for the singleton cover, gluing
  succeeds *iff* the constraint is a rectangle. Coupling is exactly the
  obstruction. (Closes the singleton-cover half of the presheaf iff, which
  was previously outlook.)
- **`allEqual`** — the n-fold all-equal coupling (generalized diagonal),
  primal graph complete, induced width n−1. Feasible set stays size |α|
  (`allEqual_encard`) but every margin is full, so the compatible families
  number |α|ⁿ.
- **`cechObstruction_allEqual`**: obstruction = |α|ⁿ − |α|, exact.
- **`cechObstruction_allEqual_ge`**: ≥ 2ⁿ − 2 for |α| ≥ 2 — the
  rectangular-representation gap is exponential in the number of variables,
  against `junctionTree_size_linear`'s n·k^(w+1) at bounded width.
- `allEqual_not_rectangular`, `allEqual_not_cechVanishes` at every arity.

Both sides of the STE bounded-width dichotomy are now machine-checked:
bounded coupling is linear, unbounded coupling is exponential.

CI run #88 green (commit b74a5a9), merged to main (50270d1). One CI
failure caught first: run #86 failed on a beta-reduction issue in
`allEqual_not_rectangular` (`hmix 0 1` un-reduced, so `rw [if_pos/if_neg]`
could not find the `ite`) — fixed by annotating the hypothesis type to
force beta, reconfirmed green.

## Q3 — Freuder width-1 tractability (`Ste.Consistency`)

The constructive counterpart: local consistency + acyclic structure →
solvable (Freuder 1982), chain case.

- `ForwardConsistent`/`BackwardConsistent`/`ArcConsistent` for a path
  network; `ChainSolution` = a genuine global selection.
- `ChainSolution.snoc`/`.cons` — single-edge extension lemmas.
- **`arcConsistent_chain_solvable`**: a nonempty arc-consistent chain has a
  global solution (greedy left-to-right via `Fin.snoc`).
- **`arcConsistent_backtrackFree`**: every value of every domain lies on a
  solution — the defining backtrack-free property.
- `chainSet_eq_feasibilitySet` bridges to the repo's `feasibilitySet`; arc
  consistency read as edge-section margin coverage ("k-consistency as
  gluing", width-1 instance).

CI run #87 green (commit a1faf0f), merged to main (56f00f1).

## Queue state after this iteration

- Q1 (lower bound + singleton-cover iff): **DONE**.
- Q3 (Freuder chain tractability): **DONE**.
- **Terminal open (documented, not faked):** the general cohomological
  programme — the full Čech Ȟ¹ functor over arbitrary covers (not just the
  singleton cover) and the quantitative "obstruction size = smallest exact
  representation blow-up" claim — plus higher-width k-consistency (forest and
  k ≥ 2 cases). These are genuine research problems, not one-citation facts;
  they are stated precisely in the notes' outlook and left open rather than
  asserted. Efficient treewidth computation stays cited-NP-hard
  (Arnborg 1987).

No new tractable sub-problems were surfaced by either agent, so the solvable
queue is drained.

## Verification discipline

Each agent's theorem statements were read and checked for faithfulness and
`sorry`/`admit`/`axiom`/`native_decide` before merge; each branch CI was
confirmed green (run #87, #88); the Q1 CI failure was caught by independent
check and fixed. Agents ran in isolated git worktrees to avoid the
shared-checkout branch-pointer race seen earlier. Documented in
`papers/notes/ste-representation-sheaves.tex` (14 pp).
