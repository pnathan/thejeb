# 2026-07-23 — Attacking the documented open question

Directive: "solve the documented open question."

The documented open items were: the general Čech Ȟ¹ functor over arbitrary
covers, the quantitative obstruction=blow-up claim, and higher-width
k-consistency. Two of these have a substantive, machine-provable core; both
are now proven and merged. The genuinely research-level residue is stated
precisely and left open — not faked.

## QA — general-cover Čech sheaf theorem (`Ste.CechCover`, merged b921ae8, CI #92)

Lifts the Čech gluing obstruction from the SINGLETON cover to an arbitrary
cover `U : J → Set V` with substantive overlaps.

- `CompatibleFamily` / `GluesCover` / `CechVanishesCover` — the Čech cocycle
  (overlap-agreement) and sheaf-gluing conditions for a general cover.
- **`rectangular_cechVanishesCover`** + **`rectangular_glueCover_existsUnique`**:
  a rectangular constraint's compatible family of local sections glues to a
  UNIQUE global section over ANY cover. Construction: choose a context per
  variable, read off the section — well-defined by overlap agreement, in the
  product by the local-section property, restricts correctly again by overlap
  agreement. A genuine sheaf theorem over arbitrary covers.
- **`cechVanishesCover_singleton_iff`**: the existing singleton-cover theory
  (`Ste.CechObstruction`, `Ste.CouplingLowerBound`) is exactly the `U = {v}`
  instance.
- **`diagonal_not_cechVanishesCover`**: gluing genuinely FAILS for the
  coupling — the rectangular theorem is non-vacuous.
- `cechVanishesCover_univ` (trivial one-context cover always glues — vanishing
  is cover-dependent), plus the H⁰-level cover obstruction number.

This mechanizes the Ȟ⁰/sheaf-gluing level of "the general Čech functor over
arbitrary covers." The FULL linearized Ȟ¹ cochain complex (cohomology as
ker/im over a free module) and the quantitative "obstruction size = smallest
exact-representation blow-up" equality remain genuinely open — noted, not
claimed.

## QB — Freuder for arbitrary rooted trees (`Ste.ConsistencyTree`, merged 18e8c20, CI #93)

Generalizes the chain (`Ste.Consistency`) to any rooted tree.

- A rooted tree on `Fin (n+1)` via `parent : Fin n → Fin (n+1)` with the
  topological-order hypothesis `(parent i).val ≤ i.val` (last node always a
  leaf). `TreeSolution`, `treeSet_eq_feasibilitySet` (bridge to feasibility).
- `TreeArcConsistent` — directional arc consistency (every parent value has a
  supporting child value).
- `truncParent` / `truncParent_le` / `castSucc_truncParent` — leaf-peeling
  truncation preserving the tree structure (the crux); `TreeSolution.snoc` —
  extension across the final edge.
- **`treeArcConsistent_solvable_from`**: backtrack-free — every root value
  extends to a global solution.
- **`treeArcConsistent_solvable`**: a nonempty directionally-arc-consistent
  rooted tree has a global solution. The full acyclic (width-1) case of
  Freuder 1982; the chain is the special case `parent i = i.castSucc`.

Higher width (k-consistency for k ≥ 2, cyclic constraint graphs) remains
genuine outlook.

## Verification discipline

Both files read for faithfulness and swept for `sorry`/`admit`/`axiom`/
`native_decide` (only docstring-prose matches). Both branch CIs confirmed
green (#92, #93) before merge; the integrated main re-verified. Agents ran in
isolated git worktrees. QA's `rectangular_cechVanishesCover` and QB's
leaf-peeling induction were traced by hand before trusting them.

## Honest boundary

I did NOT fabricate proofs of the parts that are genuinely research-level:
the full cochain-complex Ȟ¹ functor with its quantitative blow-up equality,
and k ≥ 2 / cyclic consistency. What was closed is the substantive provable
core beneath the open question — the sheaf-gluing level generalized to all
covers, and the acyclic Freuder theorem in full. Documented in
`papers/notes/ste-representation-sheaves.tex` (14 pp).
