# Dynamic frame normalization as set-valued STE

Date: 2026-07-19

## North star

The engineering target is a document database whose corpus can change over
time. Documents may be added, removed, replaced, or reprocessed. The system
extracts claims and candidate semantic frames, but must not freeze a single
normalization or coreference graph. Its normalized frame view must adapt
correctly when the active evidence changes.

The central problem is therefore not merely ordinary event coreference. It is
**dynamic, set-valued frame normalization**:

1. extract claim occurrences from the active documents;
2. associate each claim with one or more admissible frame interpretations;
3. retain multiple admissible ways of collapsing coreferent frame mentions;
4. distinguish exact identity from near-identity, anaphora, subevents, related
   events, and unresolved ambiguity;
5. iteratively eliminate invalid normalizations by intersecting property sets;
6. expose the unique normalized frame collection when it is identified, or an
   explicit residual ambiguity when it is not;
7. revise that result when documents or their derived constraints are removed.

This is a coreference-first architecture, but it is not a point-estimate
pipeline. The first stage returns an STE feasible set of normalization
hypotheses rather than committing to one clustering.

## Claims and candidate frames

For an active document set `D`, let `C(D)` be the set of immutable claim
occurrences extracted from those documents. Claim occurrences retain their
source span and document provenance even when two claims have identical
normalized text.

For each claim `c`, extraction produces a nonempty set of candidate frames

```text
Phi(c) : Set Frame
```

rather than necessarily one frame. Multiple candidates may arise from lexical
polysemy, anaphora, omitted arguments, uncertain scope, underspecified time,
or genuinely ambiguous natural speech. The stipulated quality of extraction
means the appropriate interpretation should be present in `Phi(c)`; it does
not require pretending that the interpretation is always unique.

An exact normalization hypothesis `omega` supplies at least:

- a selected frame interpretation for every claim occurrence;
- a partition of strictly coreferent frame occurrences;
- typed non-identity relations such as subevent, superevent, temporal, causal,
  repeated-instance, concept-instance, and framing-divergent relations;
- canonical role and qualifier assignments;
- provenance links back to every supporting claim and document.

The partition quotient yields a normalized and deduplicated collection. If
`P_omega` is the selected strict-coreference partition, then each block
`B in P_omega` is a set of unique claim occurrences associated with one
canonical frame under that hypothesis.

## Feasible normalizations rather than a selected partition

Let `Omega(D)` be the universe of candidate normalization hypotheses for the
active corpus. Coreference and frame constraints each denote property sets

```text
S_i(D) : Set NormalizationHypothesis
```

and the current feasible normalization set is

```text
N(D) = intersection_i S_i(D).
```

Possible criteria include:

- compatible or incompatible frame types;
- must-link and cannot-link evidence;
- participant identity and role compatibility;
- temporal and spatial compatibility;
- anaphoric accessibility;
- event granularity and whole-subevent relations;
- modality, negation, attribution, and quotation scope;
- source provenance and known source dependence;
- ontology and domain constraints.

Adding sound criteria shrinks `N(D)` monotonically. A singleton identifies the
normalization. A non-singleton is legitimate underdetermination. The system
must return that residual set or an exact abstraction of it rather than force
an arbitrary merge.

"Smallest possible valid set" refers first to the smallest feasible set of
normalization hypotheses obtained by applying all accepted constraints. It
does **not** mean the partition with the fewest canonical frames. Minimizing
frame count is a separate parsimony objective and, without justification,
systematically risks over-merging distinct events.

## The normalized output `F'` and uncertainty marker `U`

For one exact hypothesis `omega`, define

```text
F'_omega = { B | B is a block of P_omega }.
```

Every `f' in F'_omega` is therefore a set of unique, provenance-bearing claim
occurrences that denote one canonical frame under `omega`. Duplicate surface
claims may be condensed for display or scoring, but their distinct provenance
must remain recoverable.

The whole feasible set `N(D)` may contain several such outputs. The uncertainty
marker `U` should summarize disagreement among surviving exact hypotheses; it
should not conceal that disagreement inside a probability.

For claims `c` and `d`, define:

- **must-corefer** when `c` and `d` occur in the same block in every
  `omega in N(D)`;
- **cannot-corefer** when they occur in different blocks in every feasible
  hypothesis;
- **may-corefer**, marked `U`, when some feasible hypotheses merge them and
  others separate them.

The same three-valued summary can be applied to candidate frame labels, role
fillers, and typed inter-frame relations. Thus `U` is a deterministic marker of
residual feasible ambiguity. It is not necessarily a calibrated probability,
although a probabilistic layer may later rank the feasible alternatives.

A single ambiguous claim need not belong literally to several blocks inside
one exact partition. Instead it belongs to different blocks or receives
different interpretations in different feasible hypotheses. The `U` summary
is computed across those hypotheses. This preserves ordinary partition
mathematics without erasing anaphora or ambiguity.

## Dynamic document addition and removal

Document addition and removal are not symmetric implementation details.

### Addition

When a document `d` is added:

1. extract new immutable claim occurrences `C(d)`;
2. extend each old normalization hypothesis with admissible placements and
   interpretations for the new claims;
3. add the new document's provenance-indexed constraints;
4. intersect the extended universe with those constraints.

Relative to the extended universe, addition is eliminative: new evidence can
shrink the feasible hypothesis set. It may identify an old ambiguous merge,
split apparent near-duplicates, or establish a new canonical frame.

### Removal

When a document is removed, its claims and all constraints derived solely from
it must be retracted. Feasibility can expand. A previously identified cluster
may become ambiguous; a must-corefer relation may become `U`; and a canonical
frame may disappear if it has no remaining support.

Pure intersection is insufficient for deletion because intersections forget
which criterion caused an exclusion. Every criterion must therefore retain
provenance and participate in a truth-maintenance or assumption-based solving
scheme.

For each active document set `D`, define a separate feasible set `N(D)`. If
`D` is contained in `E`, restriction from the larger corpus to the smaller
corpus forgets claims in `E \ D` and maps each feasible normalization on `E`
to its induced normalization on `D`:

```text
restrict(E, D) : N(E) -> CandidateNormalization(D).
```

Not every feasible normalization on `D` must extend to one on `E`, because the
new document may rule it out. Conversely, removing the new document must allow
such previously excluded normalizations to reappear if no remaining criterion
excludes them.

This indexed family and its restriction maps are the mathematically relevant
dynamic structure. They are also the entry point for presheaf or sheaf
language: local document collections carry feasible normalizations, and
restriction forgets documents while preserving compatible structure.

## Deterministic posture toward current neural methods

Current systems commonly score mention pairs with neural encoders and apply
agglomerative clustering or graph reconstruction. That architecture typically
turns uncertain pair scores into a selected graph or partition. Early merges
can become irreversible, and pairwise thresholding can violate global
transitivity or typed event constraints.

The proposed deterministic program need not reject neural models. It can use
them for:

- candidate frame and candidate-link generation;
- ordering search or constraint propagation;
- estimating which criterion will have high reduction value;
- ranking surviving feasible hypotheses.

But a neural score should not silently become a hard exclusion. The hard layer
keeps every normalization consistent with accepted constraints. Ambiguity,
anaphora, and tension in natural speech remain explicit as multiple feasible
hypotheses and `U` summaries.

This separates three questions that probabilistic clustering often conflates:

1. Is a normalization logically admissible?
2. Which admissible normalization is best supported?
3. Has the evidence identified a unique normalization?

STE answers the first and third. Probabilistic or subjective-logic layers may
answer the second without corrupting the feasible-set semantics.

## Engineering architecture implied by the mathematics

- Store documents and extracted claim occurrences immutably; activation and
  deletion alter the active set rather than destructively rewriting history.
- Attach document and derivation provenance to every constraint.
- Treat canonical frames and clusters as materialized views of a feasible
  normalization set, not permanent records created by destructive union-find.
- Use incremental SAT/SMT/ASP, constraint programming, or an
  assumption-based truth-maintenance system so document constraints can be
  activated and retracted.
- Maintain must/may/cannot summaries for cluster membership and typed links.
- Cache exclusions with their supporting criterion sets so deletion can
  invalidate derived conclusions correctly.
- Preserve source-specific wording, framing, modality, and attribution inside
  each normalized block; deduplication must not erase evidentiary differences.

## Research questions and formal targets

1. **Order independence:** does adding the same active document set in different
   orders yield the same feasible normalization set?
2. **Retraction correctness:** after adding and then removing a document, does
   the system recover exactly the feasible set licensed by the remaining
   documents?
3. **Extension existence:** which normalizations on `D` extend to a larger
   corpus `E`?
4. **Ambiguity abstraction:** is the must/may/cannot plus `U` summary a sound
   and complete abstraction for the queries users need?
5. **Idempotence:** does adding duplicate content with dependent provenance
   leave crisp feasibility unchanged while altering only support metadata?
6. **Confluence of condensation:** do different sequences of safe merges
   produce the same exact quotient when normalization is identified?
7. **Finite representation:** can the feasible partition family be represented
   compactly without enumerating the Bell-number-sized universe?
8. **Typed relation closure:** how should strict identity interact with
   subevent, temporal, causal, and framing relations?
9. **Dynamic stability:** which changes in the active corpus cause small versus
   structural changes in the normalized frame view?
10. **Truth-stage lifting:** after coreference STE, how should every surviving
    normalized frame collection be lifted into truth-world STE without
    selecting one partition prematurely?

Immediate Lean targets should include addition monotonicity on a fixed ambient
universe, provenance-indexed criterion activation, restriction of partitions,
soundness of must/may/cannot summaries, and a retraction theorem under exact
dependency tracking.

## Revised program statement

> Given a changing collection of documents, construct and maintain the set of
> all normalized hyper-relational frame collections compatible with the active
> claims. Condense exactly coreferent claims within each feasible hypothesis,
> preserve typed non-identity relations and provenance, expose unresolved
> alternatives through a deterministic uncertainty marker `U`, and support
> correct expansion as well as contraction of the feasible set under document
> removal and addition.

This dynamic normalization layer is the engineering north star and the first
major application of STE to document semantics.
