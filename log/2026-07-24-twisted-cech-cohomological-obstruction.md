# The graded cohomological obstruction to gluing: twisted Čech coefficients

Date: 2026-07-24
Branch: `research/cohomology-obstruction`
Deliverables: `lean/Ste/TwistedCech.lean` (CI-verified), `papers/notes/cohomological-obstruction-litreview.{tex,pdf}`, `refs.bib` additions.

## The question attacked

`Ste.CechComplex` proved that the linearized Čech complex with CONSTANT
coefficients has `Ȟ¹ = 0` identically (full nerve = acyclic simplex), so
constant coefficients cannot see the coupling obstruction that the
set-level theory locates at `diagonal` / `allEqual`.  Open problem: does
a TWISTED, section-presheaf-valued Čech cohomology produce a nonzero
class that locates the coupling — the Abramsky–Mansfield–Barbosa (AMB)
program transplanted to STE — and is there a quantitative
"obstruction size = representation blow-up" relationship?  Known
subtlety going in: the AMB obstruction is sufficient but NOT necessary
(false negatives: Hardy model, AMB 2012 §5/§8; Carù 2017 refuting AMB
Conjecture 8.1 even under symmetry+connectedness).

## What was attempted

1. Built the honest twisted complex over an arbitrary cover
   `U : J → Set V` of the variable set, with coefficients the free
   `R`-module `F_R(W) = ↥(localSections T W) →₀ R` on the genuine local
   sections, restriction maps `Finsupp.lmapDomain` along section
   restriction (`sectionRes`), cochain modules `twistedC0/C1/C2`,
   coboundaries `twistedD0/D1`, complex identity, and the quotient
   `Ȟ¹`.
2. Mechanized the AMB per-section obstruction's vanishing condition
   (the extension property that AMB 2012 Prop. 4.2 proves equivalent to
   `γ(s₁) = 0`) and asked whether it can be nonzero in STE.
3. Mechanized the family-level comparison class in
   `coker(F_R(V) → Ȟ⁰)` and computed it on the diagonal's mixed family
   over the singleton cover.
4. Literature review grounding all of the above (see the PDF note),
   with web-verified bibliography (AMB 2011/2012, CSL 2015, Carù
   2017/2018, contextual fraction PRL 2017, Okay et al. 2017, Aasnæss
   2022, Bott–Tu, Combettes, Ganter–Wille).

## What closed in Lean (verbatim statements, all sorry-free, CI-green)

The twisted complex itself:

```lean
theorem twisted_d1_comp_d0 :
    (twistedD1 R T U).comp (twistedD0 R T U) = 0

abbrev twistedH0 : Submodule R (twistedC0 R T U) :=
  LinearMap.ker (twistedD0 R T U)

def twistedCoboundaries1 : Submodule R (LinearMap.ker (twistedD1 R T U)) :=
  (LinearMap.range (twistedD0 R T U)).comap
    (LinearMap.ker (twistedD1 R T U)).subtype

def TwistedH1Trivial : Prop := twistedCoboundaries1 R T U = ⊤
```

(The literal quotient TYPE `ker d¹ ⧸ im d⁰` is deliberately NOT formed:
`HasQuotient ↥(ker d¹) (Submodule R ↥(ker d¹))` fails typeclass
synthesis for these concrete `Finsupp`/`Pi` coefficient modules — a
diamond on the derived instances, pinned down by CI-run diagnostics
where `AddCommGroup ↥(ker d¹)` and `Module R (twistedC1)` synthesize
but `HasQuotient` does not.  The submodule pair carries the same
cohomology; triviality of the would-be quotient is the `Prop`
`TwistedH1Trivial`.)

Set-level compatible families are twisted 0-cocycles (AMB Prop. 3.2 in
STE):

```lean
theorem familyCochain_mem_twistedH0 {s : ∀ j, ∀ v : (U j), A v}
    (hs : CompatibleFamily T U s) :
    familyCochain R T U hs.1 ∈ twistedH0 R T U
```

**Result 1 — the structural false negative.**  The AMB per-section
extension condition (equivalent to `γ(s₁) = 0` by AMB 2012 Prop. 4.2)
holds for EVERY section of EVERY constraint over EVERY cover:

```lean
theorem amb_extension_always (j₁ : J) (s₁ : ↥(localSections T (U j₁))) :
    ∃ r ∈ twistedH0 R T U, r j₁ = Finsupp.single s₁ 1
```

Diagnosis: STE's `localSections` only contains restrictions of global
solutions, so the point masses of any global witness extend any single
section.  The transplanted per-section `Ȟ¹`-graded obstruction is
identically zero on STE section presheaves — blind to the coupling for
structural reasons (flabbiness of the section presheaf), not because
the coupling is invisible.

**Result 2 — the class that fires, one degree down.**  Over every
nontrivial commutative ring, the mixed family of the two-bit coupling
has a NONZERO class in the cokernel of the global-to-`Ȟ⁰` comparison
map:

```lean
theorem mixedFamily_not_linearlyGlues [Nontrivial R] :
    ¬ LinearlyGlues R diagonal twoCover mixedFamily_compatible.1

theorem diagonal_mixed_cocycle_not_in_globalRange [Nontrivial R] :
    (⟨familyCochain R diagonal twoCover mixedFamily_compatible.1,
        familyCochain_mem_twistedH0 R diagonal twoCover
          mixedFamily_compatible⟩ :
        ↥(twistedH0 R diagonal twoCover)) ∉
      LinearMap.range (twistedGlobalToH0 R diagonal twoCover)

theorem diagonal_twisted_obstruction_detects [Nontrivial R] :
    ¬ GluesCover diagonal twoCover mixedFamily ∧
      ¬ LinearlyGlues R diagonal twoCover mixedFamily_compatible.1
```

The cokernel statement is at REPRESENTATIVE level: a class in
`Ȟ⁰ ⧸ im(F_R(V))` is zero iff its representative lies in the image
submodule `range (twistedGlobalToH0)` (`linearlyGlues_iff_mem_range`),
and the mixed family's cocycle provably does not — the quotient-free
rendering of "the cokernel class is nonzero" (the literal quotient
type is blocked by the `HasQuotient` diamond noted above).
The proof pins the lift's coefficient at the all-true global solution
to `0` (context 0) and `1` (context 1) — the same coefficient-forcing
shape as AMB's PR-box computation.  Note this is STRICTLY stronger
than the set-level `diagonal_gluing_fails`: even signed ("negative
probability") coefficients cannot explain the mixed margins, in
deliberate contrast with the AMB world where no-signalling guarantees
a global section over the signed reals.

Soundness of the invariant (vanishing on the tractable fragment):

```lean
theorem linearlyGlues_iff_mem_range {s : ∀ j, ∀ v : (U j), A v}
    (hs : CompatibleFamily T U s) :
    LinearlyGlues R T U hs.1 ↔
      (⟨familyCochain R T U hs.1, familyCochain_mem_twistedH0 R T U hs⟩ :
          ↥(twistedH0 R T U)) ∈
        LinearMap.range (twistedGlobalToH0 R T U)

theorem GluesCover.linearlyGlues {s : ∀ j, ∀ v : (U j), A v}
    (hs : CompatibleFamily T U s) (hg : GluesCover T U s) :
    LinearlyGlues R T U hs.1

theorem rectangular_linearlyGlues (P : ∀ v, Set (A v))
    (hcover : ∀ v, ∃ j, v ∈ U j) {s : ∀ j, ∀ v : (U j), A v}
    (hs : CompatibleFamily (Set.univ.pi P) U s) :
    LinearlyGlues R (Set.univ.pi P) U hs.1
```

## What did NOT close, and why

* **The literal quotient MODULES `Ȟ¹ = ker d¹ ⧸ im d⁰` and
  `Ȟ⁰ ⧸ im F_R(V)` as types.**  `HasQuotient ↥(ker d¹)
  (Submodule R ↥(ker d¹))` fails instance synthesis for these concrete
  `Finsupp`/`Pi` coefficient modules (CI diagnostics: `AddCommGroup
  ↥(ker d¹)` and `Module R (twistedC1)` synthesize; `HasQuotient` does
  not — an instance-path diamond on submodule coercions).  All
  cohomological statements are therefore expressed at the equivalent
  submodule/representative level (`TwistedH1Trivial`,
  `linearlyGlues_iff_mem_range`); no mathematical content is lost, but
  the quotient-type presentation of `Ste.CechComplex` (which works
  because its coefficients are an abstract `[Module R M]`) does not
  transfer verbatim.  Worth a Mathlib-side minimization later.
* **The relative presheaf and the literal connecting map `γ`.**  We
  mechanized the extension condition AMB prove EQUIVALENT to
  `γ(s₁) = 0`, not the long exact sequence or the `Ȟ¹` class itself.
  Building `F̃(W) = ker(F(W) → F(W ∩ C₁))` and the snake-lemma
  connecting map is real but unattempted work; Result 1 makes its STE
  payoff moot (the class would be provably zero always).
* **Vanishing of the absolute twisted `Ȟ¹` for pairwise-disjoint
  covers.**  Conjectured (it would make Result 1 an instance of blanket
  `Ȟ¹`-triviality for singleton covers): the proof sketch goes through
  cocycle identities on empty overlaps (`F(∅) ≅ R` mass bookkeeping,
  `g j j = 0` via injectivity of restriction along propositionally
  equal sets, and a basepoint primitive with a chosen section per
  context), but the empty-overlap subtype manipulation is fiddly and
  was not machine-closed.  Stated as open in the module docstring; NOT
  claimed.
* **A nonzero twisted `Ȟ¹` class for a cover with substantive
  overlaps.**  The XOR/parity triangle (3 variables, pair contexts) is
  AvN over `Z₂` and should be detected at genuine `Ȟ¹` level even in
  the STE transplant (the per-section degeneracy argument does not
  produce a compatible linearized family when the prescribed data is a
  full stuck family); not attempted in Lean this session.
* **The quantitative rank conjecture.**  Hand computation (in the
  note, §5): for `allEqual n α`, `|α| = m`, singleton cover, field
  coefficients, the cokernel rank should be `(m−1)(n−1) =
  (m−1)·log_m(blow-up factor)` — logarithmic in the representation
  blow-up, polynomial in `n`, versus the exponential stuck-family
  count `m^n − m`.  Verified by hand for `n = m = 2` (rank 1, the two
  stuck families mapping to ± the generator).  NOT machine-checked;
  queued as a conjecture per the project rule "distrust results that
  aren't machine proven."

## Verdict

**Partially solved, with a rigorous negative component.**  A twisted,
section-presheaf-valued Čech invariant DOES locate the STE coupling
obstruction — but at graded degree 0 (the cokernel of
`F_R(V) → Ȟ⁰(U, F_R)`), not at the degree-1 per-section obstruction of
the AMB program, which is machine-provably degenerate on STE section
presheaves (`amb_extension_always`).  This is the AMB false-negative
phenomenon in structural form: an entire class of genuinely non-gluing
scenarios on which the transplanted `γ` vanishes identically.  The
degree-0 class is a genuine cohomological detector: zero exactly on
R-linearly gluable families, zero on rectangles over every cover,
nonzero on the coupling over every nontrivial ring.  The quantitative
"obstruction size = blow-up" question remains open; the literature has
no such theorem (closest: contextual fraction, PRL 2017; Aasnæss
2022), and the STE testbed suggests rank = (m−1)·log_m(blow-up) for
the coupling family.

## New conjectures for the queue

1. `twistedH1 R T U` is a subsingleton for every pairwise-disjoint
   cover with `T.Nonempty` (blanket `Ȟ¹`-triviality behind Result 1).
2. For the XOR triangle (`T = {f : Fin 3 → Bool | f 0 ⊕ f 1 ⊕ f 2 = false}`
   with the three pair contexts), the stuck family's twisted class is
   nonzero at `Ȟ¹` proper (AvN over `Z₂` fires in STE).
3. Rank conjecture: `rank coker(F_R(V) → Ȟ⁰) = (m−1)(n−1)` for
   `allEqual n α`, `|α| = m ≥ 2`, field coefficients, singleton cover;
   equivalently `(m−1)·log_m` of the rectangular blow-up factor.
4. `obstructionClass_eq_zero_iff` + `cechVanishes_iff_rectangular`
   suggest: for the singleton cover, the class vanishes for ALL
   compatible families iff `T` is rectangular — an exact
   linear-cohomological characterization of tractability (the ⇐
   direction is proven; ⇒ requires producing a stuck family from
   non-rectangularity and showing its class nonzero in general, which
   needs the margin-pinning argument beyond point determinacy).

## Process notes

* CI (`lean.yml`) is the only verifier used; no local Lean build.
  First push failed on (a) missing `noncomputable` for Finsupp-based
  defs and (b) a `HasQuotient` instance-synthesis failure at the
  quotient abbrevs, with cascading signature corruption downstream;
  fixed by `noncomputable section` (and see the CI history for the
  diagnostic `example : _ := inferInstance` iteration).  The entire
  mathematical core (complex identity with proof-irrelevant `abel`
  atoms, cocycle membership, the degeneracy theorem, and the
  coefficient-pinning contradiction) elaborated correctly on the first
  attempt.
* Literature facts were web-verified (arXiv/EPTCS/LIPIcs/PRL);
  the note's bibliography contains no fabricated entries; two items
  are cited as preprints because no journal version exists (Carù 2018,
  Aasnæss 2022).
