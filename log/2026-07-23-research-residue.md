# 2026-07-23 — The research-level residue: linearized Ȟ¹ + higher-width consistency

Directive: perform the Lean research on the two remaining research-level items —
the full linearized Ȟ¹ cochain complex + obstruction=blowup equality, and
higher-width k-consistency (k ≥ 2, cyclic).

Both were attacked. The substantive, provable core of each is now mechanized and
merged; the genuinely hard tail is documented precisely, not faked.

## R1 — linearized Čech cochain complex (`Ste.CechComplex`, merged 4c6fe69, CI #98)

The Abramsky–Brandenburger module-level machinery. Over any `CommRing R` and
`R`-module `M`:

- Cochains `C⁰=(ι→M)`, `C¹`, `C²`, `C³` with alternating coboundaries
  `cechD0/D1/D2` (`(d⁰f)ᵢⱼ = fⱼ − fᵢ`, etc.).
- **`cechComplex_d_comp_d`** and **`cechComplex_d2_comp_d1`**: `d¹∘d⁰ = 0`,
  `d²∘d¹ = 0` — a genuine cochain complex.
- Cohomology as quotient modules: `cechH0 = ker d⁰`, `cechH1 = ker d¹ / im d⁰`,
  `cechH2 = ker d² / im d¹`. Exactness `ker d¹ = im d⁰` (basepoint primitive) ⇒
  **`cechH1_subsingleton`**, `cechH2_subsingleton` (Ȟ¹ = Ȟ² = 0 for the
  constant-coefficient full nerve — an acyclic simplex); `cechH0 ≃ₗ M`.
- STE bridge: `globalZeroCochain` linearizes a section into the free module
  `(∀v, A v) →₀ R`, proven a 0-cocycle (`globalZeroCochain_mem_cechH0`) and
  injective; `CompatibleFamily.exists_cechH0` sends set-level `CechCover` gluing
  into the linearized Ȟ⁰.

Delivers the "cohomology as ker/im over a free module" the open item named. One
CI failure first (`globalZeroCochain` needed `noncomputable`, since
`Finsupp.single` is noncomputable — a codegen issue, not a proof gap), fixed.

**Genuinely open (not claimed):** a nonzero *graded* Ȟ¹ locating the coupling —
which needs twisted/locally-varying coefficients or a non-full nerve, not the
constant coefficients that vanish here — and the quantitative "obstruction size =
smallest-representation blow-up" equality.

## R2 — higher-width / cyclic directional consistency (`Ste.AdaptiveConsistency`, merged 55afa75, CI #101)

Generalizes the width-1 tree by replacing a node's single parent with a
separator `sep i : Finset` of earlier neighbours (any size).

- `DirectionalConsistent` / `SepSupported` (separator scope); `AdaptiveSolution`.
- **`directionalConsistent_solvable`**: a nonempty directionally-consistent
  bucket network has a global solution. Via the faithful Dechter
  `prefixConsistent_solvable_from` (earlier-variables-only dependence), leaf-peel
  induction.
- **`twoParent_solvable`**: the genuinely cyclic width-2 (k=3) case — two earlier
  neighbours, ternary bucket — out of reach of the tree formalism.
- `treeArcConsistent_solvable_of_adaptive`: the tree is the `sep i = {parent i}`
  special case; `sepWidthLE_pair` marks width-2 = cyclic.

Dechter adaptive consistency / Freuder strong-k-consistency-plus-width.

**Honest deviation (agent-caught, verified):** the naive directional-consistency
statement is *false* — it is vacuous when a later domain is empty while
solvability fails. The theorem therefore carries `∀ u, (D u).Nonempty`, and the
faithful root-value analogue is proven for the stronger `PrefixConsistent`
(Dechter's actual definition). This is exactly the kind of flaw that
machine-checking surfaces.

**Genuinely open (not claimed):** the *enforcement* half (that bucket
elimination establishes directional consistency at width-bounded cost, preserving
solutions); full both-orientation backtrack-freeness; the formal link
`SepWidthLE` ↔ `Ste.GraphTreewidth` induced width; the converse (width ≥ k where
k-consistency fails).

## Verification discipline

Both files read for faithfulness and non-vacuity (esp. `twoParent_solvable` as a
real cyclic witness; `cechH1_subsingleton` honestly scoped to the constant nerve)
and swept for `sorry`/`admit`/`axiom`/`native_decide`. Both branch CIs confirmed
green (#98, #101); the integrated main re-verified. Agents in isolated worktrees.
Two CI failures caught by independent check and fixed (`noncomputable`;
`Fin.snoc` motive ascription). Documented in
`papers/notes/ste-representation-sheaves.tex` (16 pp).

## Net

The named research-level items are now half-mechanized in the honest sense: the
linearized cohomology machinery exists and computes (vanishing + bridge), and
bounded-width/cyclic tractability is proven. What remains is a small, sharply
stated set of genuine research problems (graded nonzero Ȟ¹ + obstruction=blowup;
consistency enforcement; the width-formalism link) — left open, not fabricated.
