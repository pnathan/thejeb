# Dynamic set-valued frame normalization: literature review and research program

Date: 2026-07-19

Status: research synthesis and mechanization companion to
`Ste.DynamicFrame`

## Executive finding

The proposed system is not best described as another event-coreference
clusterer. It is a **provenance-indexed possible-worlds system for dynamic
frame normalization**.

For every active document set, it maintains the set of exact frame
interpretations and strict-coreference partitions compatible with the accepted
constraints. It then publishes only conclusions that are invariant across that
set, together with an explicit `U` relation for conclusions on which feasible
hypotheses disagree. Document insertion activates provenance-supported
constraints and can eliminate worlds. Document deletion deactivates those
constraints and can restore worlds.

This formulation joins five literatures that are usually treated separately:

1. cross-document event coreference and event relation extraction;
2. ambiguity, quasi-identity, and underspecified anaphora;
3. incomplete databases and certain answers over possible worlds;
4. truth maintenance, provenance, and incremental view maintenance;
5. set-theoretic estimation and local-to-global consistency.

The first literature supplies candidates and learned compatibility evidence.
The second prevents an invalid collapse of identity into a binary pair label.
The third supplies the semantics of `must`, `may`, and `cannot`. The fourth
supplies correct insertion and retraction. STE supplies the monotone
constraint-intersection layer. Presheaf and sheaf language may later describe
restriction and gluing across document subcollections, but it is not required
for the first executable system.

The central mathematical result is simple and consequential. Each exact
hypothesis has an equivalence relation `~_h` over claim occurrences. The
relation

```text
c ~must d  iff  for every feasible h, c ~_h d
```

is the intersection of equivalence relations and is therefore itself an
equivalence relation. It defines a safe deterministic quotient. By contrast,
the relation “some feasible hypothesis merges these claims” need not be
transitive and cannot safely define a partition. `U` must therefore be an
overlay between must-coreference classes, not a special kind of equivalence
class.

## Reflection on the research conversation

The initial temptation was to say that identity resolution and claim truth
must be solved jointly from the beginning. That was too coarse. It obscured a
stronger architecture already implicit in the project.

The corrected architecture is coreference-first in **type**, but not in
**commitment**. Its first output is not one partition. It is a feasible set of
partitions and frame interpretations. This retains all admissible antecedents,
frame senses, clusterings, and typed near-identity links. Only after this
normalization feasible set has been narrowed do we lift each surviving world
into the truth-stage STE system.

That distinction resolves a false dichotomy:

- point-estimate coreference-first pipelines are brittle because an early
  merge is treated as fact;
- fully joint inference is not necessary to avoid that brittleness;
- set-valued coreference-first inference retains uncertainty without mixing
  all downstream semantics into the normalization kernel.

The engineering north star sharpens the science. A static benchmark asks for
one clustering of one frozen corpus. A document database asks for a family of
answers indexed by active document sets, with laws relating those answers.
Addition and removal expose whether the semantics is real or merely an
artifact of an irreversible clustering algorithm.

The phrase “smallest valid set” also needs a fixed interpretation. It means the
smallest feasible **set of normalization hypotheses** after applying all sound
constraints. It does not mean the partition with the fewest clusters.
Minimizing cluster count is an optional parsimony objective and encourages
over-merging when used as semantics.

## Scope and terminology

### Claim occurrence

A claim occurrence is an immutable, provenance-bearing extracted unit. Two
occurrences can have identical normalized text and remain distinct because
they came from different sources, quotations, times, or discourse contexts.

The project stipulates high-quality hyper-claim extraction: the system can
extract the relevant proposition-like unit and a nonempty candidate set of
appropriate structured frames. The normalization problem begins after that
stipulation.

### Frame and hyper-relational fact

“Hyper frame” is understandable project shorthand, but the literature uses
several overlapping terms:

- semantic frame for an event or situation with typed roles;
- n-ary relation or event record for one predicate plus several arguments;
- hyper-relational fact for a base relation qualified by time, source,
  modality, attribution, or other key-value qualifiers;
- nested fact when a fact itself is an argument of another fact;
- event graph or semantic graph when relations among events are first-class.

The most portable program term is **provenance-bearing hyper-relational
frame**. “Frame” preserves the linguistic role structure; “hyper-relational”
signals qualifiers and n-ary structure; “provenance-bearing” prevents
deduplication from erasing evidence.

### Identity is not general relatedness

Strict event identity should remain an equivalence relation. Subevent,
superevent, causation, temporal succession, repeated instance, schema-instance,
and framing divergence are typed non-identity relations. Treating all semantic
similarity as coreference destroys both the quotient and the evidence that two
sources are describing related but distinct events.

## Literature review

### 1. Document and multi-document claim extraction

Deng et al., *Document-level Claim Extraction and Decontextualisation*
([ACL 2024](https://aclanthology.org/2024.acl-long.645/)), shows that extracting
self-contained claims from a document is itself a document-level task: local
sentences often require recovered entities, time, and context. This supports
immutable claim occurrences with explicit decontextualization provenance,
rather than treating isolated sentences as database facts.

Min et al., *Multi-Document Event Extraction Using Large and Small Language
Models* ([EMNLP 2025](https://aclanthology.org/2025.emnlp-main.972/)), moves
toward canonical multi-document event records and uses FrameNet-style
arguments. It is close to the engineering target, but canonicalization still
aims to produce extracted event objects rather than a complete family of
admissible canonicalizations under deletion.

The stipulation in this project deliberately brackets extraction accuracy.
That is methodologically useful: it isolates the normalization semantics from
the empirical question of whether a model generated all viable candidates.
Candidate generation can later be evaluated by recall; the constraint kernel
can be evaluated by soundness and dynamic laws.

### 2. Current cross-document event-coreference methods

The current center of gravity is learned pair or cluster scoring followed by a
graph or clustering procedure.

Clark and Manning's entity-level model
([ACL 2016](https://aclanthology.org/P16-1061/)) helped establish learned
cluster-level merge decisions. Later cross-document work combines contextual
encoders with pair scoring, discourse signals, graph reconstruction, and
agglomerative clustering. Examples include:

- Held et al., *Focus on What Matters: Applying Discourse Coherence Theory to
  Cross Document Coreference*
  ([EMNLP 2021](https://aclanthology.org/2021.emnlp-main.106/));
- Cattan et al., *Cross-document Coreference Resolution over Predicted
  Mentions* ([ACL Findings 2021](https://aclanthology.org/2021.findings-acl.453/)),
  which addresses scalability by splitting documents and later merging
  meta-clusters;
- De Langhe et al., *Graph-based cross-document event coreference resolution*
  ([LREC-COLING 2024](https://aclanthology.org/2024.lrec-main.541/));
- Ahmed et al., *X-AMR: Cross-document Abstract Meaning Representation*
  ([LREC-COLING 2024](https://aclanthology.org/2024.lrec-main.920/));
- Zhao et al., *Building a Richer Cross-Document Event Coreference Resolution
  Dataset* ([NAACL 2025](https://aclanthology.org/2025.naacl-long.178/)), whose
  RECB evaluation makes identity/near-identity confusions substantially more
  visible than ECB+;
- De Langhe et al., *Position-aware end-to-end cross-document event
  coreference resolution* ([Natural Language Processing Journal
  2025](https://www.sciencedirect.com/science/article/pii/S2949719125000603)).

The learned systems are valuable candidate generators and rankers. The
semantic issue is that a real-valued pair score plus a threshold is not an
identity relation. Agglomeration repairs transitivity operationally by choosing
clusters, but it normally returns one answer and makes early merge choices
costly to retract. Graph reconstruction improves global coherence but still
usually optimizes one selected graph.

Benchmark design also matters. ECB+META
([ACL 2024](https://aclanthology.org/2024.acl-short.27/)) shows that standard
event-coreference evaluation can reward lexical or lemma leakage. MCECR
([NAACL Findings 2024](https://aclanthology.org/2024.findings-naacl.245/))
extends the multilingual setting. EventRelBench
([EMNLP Findings 2025](https://aclanthology.org/2025.findings-emnlp.482/))
evaluates coreference alongside temporal, causal, and super/subevent
relations. Together these results argue against a single untyped similarity
edge as the central object.

The literature therefore supports the user's empirical diagnosis: neural and
graph/agglomerative methods dominate performance work. It does not yet make a
dynamic, deletion-correct possible-worlds semantics the standard output.

### 3. Partial identity, quasi-identity, and ambiguity

The strongest conceptual support comes from work that refuses to reduce all
event relation to binary identity.

Hovy et al., *Events Are Not Simple: Identity, Non-Identity, and
Quasi-Identity* ([EVENTS 2013](https://aclanthology.org/W13-1203/)), argues that
event identity judgments are affected by incomplete world knowledge and that
quasi-identity relations must be represented. Pratapa et al., *Cross-document
Event Identity via Dense Annotation*
([CoNLL 2021](https://aclanthology.org/2021.conll-1.39/)), develops dense
identity and quasi-identity annotation. Asr and Demberg
([TextGraphs 2014](https://aclanthology.org/W14-2906/)) explicitly observe that
a hard cluster choice rules out partial coreference, whereas unconstrained
pairwise representation can be non-transitive; they discuss soft clustering
and incremental settings.

Bos, *Unresolved Anaphora and Underspecification*
([Ambiguity in Anaphora 2006](https://aclanthology.org/W06-39.pdf)), treats
multiple potential interpretations as a representation-and-inference problem,
not merely an error awaiting a classifier. Some ambiguity is deictic or
structurally underdetermined and may never resolve from the available text.
Scalar Anaphora
([CRAC 2023](https://aclanthology.org/2023.crac-main.4/)) similarly studies
degrees between identity, near identity, bridging, and nonidentity.

Nedoluzhko et al.
([CorefUD 2013](https://aclanthology.org/W13-3726/)) reports that annotating an
explicit near-identity category is difficult and that annotator disagreement
can be a more faithful ambiguity signal. This is directly aligned with `U`:
uncertainty can be defined extensionally by disagreement among surviving exact
interpretations, rather than requiring a human or model to assign a mysterious
“ambiguous” label in isolation.

Two very recent resources further strengthen the case:

- FRECO ([EMNLP 2025](https://aclanthology.org/2025.emnlp-main.1440/)) studies
  framing-divergent event coreference in contentious topics and includes
  partial or near-coreferential phenomena;
- AmbiCoRefVis ([LREC 2026](https://aclanthology.org/anthology-files/anthology-files/pdf/lrec/2026.lrec-main.144.pdf))
  visualizes multiple global coreference interpretations and notes that
  ambiguity creates combinatorially many possible chains.

ABCD-LINK ([EACL 2026](https://aclanthology.org/2026.eacl-long.157/)) broadens
cross-document linking beyond exact coreference and reports a retrieval plus
LLM workflow for fine-grained links. This is the direction the frame relation
layer should take: strict identity for quotienting; typed links for everything
else.

### 4. Hyper-relational representation

RDF 1.2 supplies a standards-level model for graph facts and modern
reification mechanisms
([W3C RDF 1.2 Concepts](https://www.w3.org/TR/rdf12-concepts/)). It is useful
for interchange and provenance, but a plain triple graph is too weak as the
mathematical normalization object unless event roles and qualifications are
reified carefully.

Recent hyper-relational knowledge-graph work explicitly addresses qualifiers,
temporality, and nesting. UniHR
([2024](https://arxiv.org/abs/2411.07019)) offers a unified representation for
hyper-relational, temporal, and nested facts. A recent n-ary knowledge-graph
taxonomy ([2025](https://arxiv.org/abs/2506.05626)) emphasizes that n-ary and
hyper-relational structures are not interchangeable implementation trivia.
Generative hyper-relational fact work
([2026](https://arxiv.org/abs/2605.24064)) shows that models are beginning to
generate structured qualified facts directly.

These representations are compatible with the project but do not solve its
identity semantics. A hyper-relational fact is the content of one candidate
frame interpretation. A normalization hypothesis additionally selects which
claim occurrences share one canonical frame and which typed relations connect
distinct frames.

The representation should minimally retain:

- frame type and trigger;
- typed role fillers;
- time, location, modality, polarity, attribution, and quotation scope;
- source document, source span, extractor/version, and derivation provenance;
- typed inter-frame links;
- enough source wording to compare framing rather than erase it.

### 5. Incomplete databases and possible-world semantics

The possible-worlds literature supplies the cleanest semantics for the desired
output. Imieliński and Lipski's foundational account of incomplete relational
databases ([JACM 1984](https://dl.acm.org/doi/10.1145/1634.1886)) represents an
incomplete database compactly as a set of possible complete databases. Modern
surveys retain this core idea: a query answer is **certain** when it holds in
every represented world and possible when it holds in at least one
([Kimelfeld and Ré 2024](https://dl.acm.org/doi/fullHtml/10.1145/3624717)).

Substitute “exact normalization hypothesis” for “complete database” and the
project's summary follows immediately:

```text
must(c,d)       = same(c,d) in every feasible world
may(c,d)        = same(c,d) in at least one feasible world
cannot(c,d)     = different(c,d) in every feasible world
U(c,d)          = may-same(c,d) and may-different(c,d)
inconsistent    = there is no feasible world
```

The last case is essential. If the feasible set is empty, both universal
statements “all worlds merge” and “all worlds split” are vacuously true.
Therefore `must`, `cannot`, and `U` are not a complete status system unless
consistency is checked first. The mechanization makes this premise explicit.

ULDBs add lineage to uncertain data
([VLDB 2006](https://www.vldb.org/conf/2006/p953-benjelloun.pdf)). Provenance
semirings give a general algebraic account of which input facts support an
output
([Green, Karvounarakis, and Tannen 2007](https://web.cs.ucdavis.edu/~green/papers/pods07.pdf)).
These are highly relevant to document deletion: an output conclusion must
carry an expression over the documents and derived constraints that support
it, so retraction can invalidate exactly the affected conclusions.

Possible worlds have a known combinatorial cost. A corpus with `n` candidate
mentions has Bell-many possible partitions even before frame senses are
included. Compact representation is therefore central, not optional. The
cluster-trellis work on representing uncertainty over all partitions
([NeurIPS 2018](https://proceedings.neurips.cc/paper/2018/hash/29c4a0e4ef7d1969a94a5f4aadd20690-Abstract.html))
is a useful algorithmic analogue. BDDs, ZDDs, d-DNNF, SAT model sets, ATMS
labels, or specialized partition diagrams are plausible representations.

### 6. Truth maintenance, deletion, and incremental computation

Doyle's Truth Maintenance System
([Artificial Intelligence 1979](https://dspace.mit.edu/entities/publication/5377b306-4ecc-4687-b1f5-78cbb4a0543a))
records reasons for beliefs and revises them incrementally. De Kleer's
Assumption-based TMS maintains multiple contexts simultaneously
([Artificial Intelligence 1986](https://www.sciencedirect.com/science/article/pii/0004370286900809));
his retrospective emphasizes this multiple-context capability
([1993](https://www.dekleer.org/Publications/A%20Perspective%20on%20Assumption-based%20truth%20maintenance.pdf)).

This is almost exactly the control-plane semantics needed here. Treat document
activation and contestable extraction decisions as assumptions. Constraint
derivations carry environments identifying the assumptions on which they
depend. An ATMS label compactly records the environments in which a conclusion
holds. Removing a document retracts its assumption and changes the live
environments without recomputing the conceptual model from scratch.

Incremental database work supplies a complementary data plane. Differential
dataflow handles iterative computations under changing collections
([CIDR 2013](https://www.cidrdb.org/cidr2013/Papers/CIDR13_Paper111.pdf)). DBSP
provides an algebraic foundation for incremental view maintenance with both
insertions and deletions
([VLDB 2023](https://www.vldb.org/pvldb/vol16/p1601-budiu.pdf)). These systems do
not automatically enumerate normalization worlds, but their treatment of
signed changes and materialized views is the right implementation model for
active claims, candidate edges, provenance, and summary queries.

Dynamic correlation clustering studies online vertex additions/deletions and
edge changes ([2022](https://arxiv.org/abs/2211.07000)); consistent online
clustering studies the recourse cost of changing assignments
([ICML 2022](https://proceedings.mlr.press/v162/cohen-addad22a/cohen-addad22a.pdf)).
These results are useful for performance bounds and approximate ranking, but
their objective is normally one changing clustering. The research program
needs a different primary invariant: exact agreement with the feasible-world
semantics, followed by an explicit policy for approximation.

### 7. Constraint languages and paraconsistency

Must-link and cannot-link constraints are standard in constrained clustering
([survey, 2022](https://arxiv.org/html/2212.14437v3)). Frame normalization
requires a richer language: equivalence, typed incompatibility, role
functionality, temporal/spatial disjointness, anaphoric accessibility,
whole/subevent relations, source dependence, and qualifier preservation.

Contradictory extracted constraints should not be confused with ambiguity.
Ambiguity means several feasible worlds remain. Contradiction means no world
satisfies all currently hard constraints. A production system needs a policy
for the second case: quarantine suspect constraints, compute minimal
inconsistent supports, downgrade a rule from hard to defeasible, or use a
paraconsistent query layer. Belnapian four-valued semantics distinguishes true,
false, both, and neither; recent work applies these values to querying
inconsistent knowledge bases
([KR 2024](https://proceedings.kr.org/2024/14/kr2024-0014-bienvenu-et-al.pdf)).

This yields a useful separation:

- `U` means at least one merge world and at least one split world survive;
- `inconsistent` means no world survives;
- `both-supported` means positive and negative evidence exists in a
  paraconsistent evidence layer, which may or may not make the hard STE layer
  inconsistent.

### 8. STE and local-to-global topology

Combettes's set-theoretic estimation formulation models each observation as a
property set and the answer as their intersection. The existing `Ste.Basic`
module mechanizes the core antitonicity theorem: activating more constraints
can only shrink the feasible set.

For active document sets `D`, define `N(D)` as the feasible normalizations.
On a fixed ambient universe of claims and hypotheses,

```text
D subset E  implies  N(E) subset N(D).
```

This is the formal insertion/deletion law implemented now. When the hypothesis
universe itself changes with the active claims, restriction maps forget claims
from removed documents. The family then becomes presheaf-like: document
subcollections carry local normalization spaces and inclusions induce
restriction.

Applied sheaf work uses local sections, compatibility, and gluing to formalize
data consistency. Robinson's survey
([2016](https://arxiv.org/abs/1604.04647)) and sheaf-based uncertainty
quantification
([2020](https://pmc.ncbi.nlm.nih.gov/articles/PMC7349656/)) are the most relevant
foundations. A broad recent review maps sheaves across data science and machine
learning ([2025](https://arxiv.org/abs/2502.15476)). Work on model presheaves
([2021](https://arxiv.org/pdf/2105.10414)) makes local data/local model
assignments explicit. A 2026 Lean formalization of multi-view consistency
([Gibson 2026](https://arxiv.org/abs/2605.08609)) shows that a concrete
restriction-and-gluing theorem can be machine-checked.

Sheaf language should be earned rather than ornamental. The immediate object
is an antitone feasible-set map over active documents. It becomes a genuine
presheaf when exact restriction maps and functor laws are defined. It becomes
a sheaf only if compatible local normalizations have a unique global gluing.
Natural language may fail existence because local interpretations conflict,
and may fail uniqueness because cross-document identity remains ambiguous.
Those failures are scientifically interesting: obstruction detects conflict;
non-unique gluing is precisely residual global ambiguity.

## Proposed mathematical object

Fix ambient types:

```text
Document, Claim, Frame, Hypothesis, Constraint.
```

Each claim has immutable source ownership and a nonempty candidate-frame set:

```text
owner : Claim -> Document
Phi   : Claim -> Set Frame
Phi(c) is nonempty.
```

Each exact hypothesis `h` supplies:

```text
interpret_h : Claim -> Frame
same_h      : Claim -> Claim -> Prop
```

with `interpret_h(c) in Phi(c)` and `same_h` an equivalence relation. In a
larger version it also supplies roles, qualifiers, and typed relations between
distinct equivalence classes.

Each constraint `k` has a document support set and denotes an STE property
set:

```text
support(k) : Set Document
S_k        = {h | h satisfies k}.
```

For active documents `D`:

```text
K(D) = {k | support(k) subset D}
N(D) = intersection over k in K(D) of S_k.
```

This support rule handles a constraint derived jointly from several
documents: it is active only while all required sources are active. Rules or
ontology constraints with empty support are always active.

For a consistent `N(D)`, define:

```text
Must_D(c,d)   iff forall h in N(D), same_h(c,d)
May_D(c,d)    iff exists h in N(D), same_h(c,d)
Split_D(c,d)  iff exists h in N(D), not same_h(c,d)
Cannot_D(c,d) iff forall h in N(D), not same_h(c,d)
U_D(c,d)      iff May_D(c,d) and Split_D(c,d).
```

Exactly one of `Must`, `Cannot`, and `U` holds for a consistent feasible set.
An empty feasible set has the separate status `inconsistent`.

Every exact world produces the requested result

```text
F'_h = Claim / same_h,
```

restricted to active claims. The deterministic published quotient is

```text
F'_must = Claim / Must_D.
```

Each element of `F'_must` is a set of unique claim occurrences that are
coreferent under every admissible exact normalization. `U` edges connect
different must-classes when at least one admissible world would merge them.
Cannot edges record pairs no admissible world merges. This structure is more
informative and more mathematically valid than trying to put an ambiguous
claim into several blocks of one partition.

The truth stage is a lift over worlds. If `T(h)` is the STE truth feasible set
conditioned on normalization `h`, then the combined feasible object is

```text
{(h,t) | h in N(D) and t in T(h)}.
```

Truth claims can again be summarized by universal and existential
quantification. This preserves the coreference-first modular boundary without
discarding normalization uncertainty.

## Mechanization delivered in `Ste.DynamicFrame`

The current Lean module formalizes the fixed-ambient-universe kernel:

- nonempty candidate frame sets and per-hypothesis interpretations;
- exact strict-coreference equivalence for every hypothesis;
- document-supported constraints;
- active claim and active constraint views;
- the STE feasible normalization set;
- antitonicity under document addition;
- `MustSame`, `MaySame`, `MaySeparate`, `CannotSame`, and `Uncertain`;
- proof that `MustSame` is an equivalence relation;
- the safe quotient `CanonicalFrame`;
- exhaustive must/cannot/uncertain classification for consistent corpora;
- persistence laws for must/cannot facts under added constraints;
- reverse monotonicity of existential possibilities.

The fixed ambient universe is deliberate. It makes retraction an activation
change rather than deletion of mathematical objects. Production storage can
garbage-collect inactive records while retaining stable identifiers and an
audit log.

## Engineering design

### Storage

Use immutable tables for documents, claim occurrences, candidate frames,
candidate links, and derived constraints. Store active-document membership
separately. Every derived constraint records its support expression, rule
version, and derivation.

Do not treat canonical clusters as authoritative mutable rows. They are
materialized views with stable presentation identifiers where possible.
Deletion must be able to split a former display cluster or restore a formerly
excluded hypothesis.

### Solver kernel

A practical first kernel can use SAT/SMT/ASP or CP-SAT:

- variables select one candidate frame interpretation per claim;
- variables represent pairwise same-frame decisions or cluster assignments;
- hard clauses enforce equivalence and typed compatibility;
- assumption literals activate document-supported clauses;
- incremental solving reuses learned state across insertions/deletions;
- model enumeration or a compiled representation answers must/may queries.

Pairwise variables require transitivity constraints, which are cubic if
materialized naively. Lazy transitivity cuts, representative variables,
correlation-clustering formulations, or partition diagrams should be
benchmarked.

Neural models remain useful for high-recall candidate generation and search
ordering. A score should become a hard exclusion only through an explicit,
auditable policy. Otherwise it is a ranking over feasible worlds.

### Summary queries

For each candidate pair, two satisfiability checks suffice conceptually:

```text
SAT(N(D) and same(c,d))
SAT(N(D) and not same(c,d)).
```

The outcomes are:

| same SAT | split SAT | status |
|---|---|---|
| no | no | inconsistent kernel or unreachable pair context |
| yes | no | must |
| no | yes | cannot |
| yes | yes | `U` |

Incremental assumptions and unsat cores can explain why a pair is must or
cannot. ATMS labels or compiled model sets can answer many such queries more
efficiently than independent enumeration.

### Retraction protocol

On document removal:

1. deactivate the document assumption;
2. deactivate claims in the public active view;
3. retract constraints whose support is no longer contained in the active set;
4. update the compact feasible-world representation;
5. recompute affected must/cannot/`U` summaries;
6. update canonical-frame materialized views while preserving provenance;
7. emit a semantic diff explaining merges, splits, appearances, and removals.

The correctness target is extensional: the incremental result must equal a
fresh computation from precisely the remaining active documents.

## Evaluation program

Static CoNLL F1 is insufficient. The program needs four evaluation families.

### Candidate completeness

Measure whether the gold frame sense, antecedent, and strict/typed relation
remain in the generated candidate space. This evaluates the stipulated front
end when the stipulation is relaxed.

### Possible-world calibration

For ambiguous cases with multiple defensible annotations, measure:

- coverage: at least one feasible world matches each defensible reading;
- exclusion precision: rejected readings are genuinely invalid;
- certain-answer precision: published must/cannot facts are correct;
- ambiguity precision/recall: `U` appears exactly where defensible worlds
  disagree.

AmbiCoRefVis-style multi-interpretation data, FRECO, RECB, and dense
quasi-identity annotations are promising starting points, but a dedicated
dynamic corpus will be needed.

### Dynamic laws

Generate document insertion/removal sequences and test:

- order independence for the same final active set;
- add-then-remove round trips;
- equivalence between incremental and from-scratch recomputation;
- idempotence of duplicate activation events;
- stable provenance and explanation after cluster splits;
- bounded update latency and memory.

Property-based testing can generate small finite hypothesis universes and
compare the solver against exhaustive enumeration.

### Downstream truth robustness

Compare a point-estimate pipeline with the set-valued lift. Measure how often a
truth conclusion changes solely because an early coreference merge was wrong,
and whether must-truth conclusions remain valid across all feasible
normalizations.

## Novel open questions

1. **Compact exact representation.** What representation supports efficient
   insertion, deletion, `must/may` queries, and explanation over a constrained
   set of partitions with candidate frame senses?

2. **Canonical identity under retraction.** Can presentation identifiers for
   must-classes remain stable through splits and re-merges without smuggling an
   old point estimate into semantics?

3. **Minimal sufficient support.** Can every must/cannot conclusion be
   accompanied by minimal document supports, and can those supports be updated
   incrementally?

4. **Typed quasi-identity algebra.** Which relations compose soundly? For
   example, what can be inferred from strict identity followed by subevent,
   near identity, or framing divergence?

5. **Candidate-generation fairness.** STE cannot preserve a world that the
   neural candidate generator never proposes. How can candidate recall be
   certified or bounded?

6. **Constraint fairness and repair.** When `N(D)` becomes empty, which minimal
   inconsistent supports identify an unfair extraction or rule, and what
   deterministic repair policy is justified?

7. **Presheaf exactness.** With corpus-dependent claim universes, do restriction
   maps satisfy identity and composition? Which compatible local
   normalizations extend globally, and when is the extension unique?

8. **Topology of ambiguity.** Can obstruction or cohomology distinguish local
   contradiction from non-unique global identity, and does that yield useful
   algorithms rather than vocabulary alone?

9. **Finite convergence.** Under iterative addition of sound criteria, when
   does the feasible family reach a fixed point? Can redundancy and reduction
   value be computed without enumerating all worlds?

10. **Truth lift commutation.** Under what conditions does normalizing first and
    then applying truth constraints give the same certain answers as a fully
    joint system?

11. **Probabilities without semantic corruption.** Can calibrated mass be
    placed over feasible worlds while preserving crisp must/cannot guarantees
    and representing source dependence?

12. **Privacy and deletion semantics.** If a document must be forgotten rather
    than merely deactivated, what cached proofs, learned clauses, embeddings,
    and provenance expressions must also be removed to make semantic and
    physical deletion agree?

## Recommended research sequence

1. Finish the finite crisp kernel: exact hypotheses, document assumptions,
   strict identity, typed nonidentity, and must/may/cannot queries.
2. Build a tiny exhaustive reference implementation and a property-based
   dynamic-law suite.
3. Encode the same problems incrementally in SAT/SMT or ASP; compare compiled
   representations and explanation quality.
4. Create a dynamic benchmark by taking multi-document event datasets and
   adding annotated insertion/removal sequences plus alternative defensible
   interpretations.
5. Lift claim-truth STE over the feasible normalization family.
6. Only then add probabilistic rankings and learned search heuristics.
7. Develop the corpus-indexed presheaf and prove restriction laws; test whether
   sheaf or obstruction machinery provides nontrivial diagnostics.

## Bottom line

The program is novel primarily in its **combination and invariant**, not
because none of its ingredients exists. NLP supplies sophisticated learned
identity signals and increasingly rich event relations. Ambiguity research
supplies multiple interpretations and quasi-identity. Incomplete databases
supply possible worlds and certain answers. ATMS and provenance supply
retraction. Incremental databases supply efficient signed updates. STE
supplies feasibility by intersection. Sheaf theory supplies a possible later
local-to-global account.

The research contribution is to make these pieces one deletion-correct
normalization semantics, then mechanize the laws that a live document system
must obey. The safe public object is not one guessed partition. It is a
must-coreference quotient, a typed relation graph, explicit `U` edges, and the
provenance-indexed feasible family from which all three are derived.
