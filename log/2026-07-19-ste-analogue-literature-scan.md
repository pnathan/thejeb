# STE analogue literature scan: Holmesian feasible-space refinement

Date: 2026-07-19

Project motto for this pass: Holmes' dictum, in STE language, is the singleton
case of feasibility refinement: eliminate property-set violations until the
remaining feasible set is either empty (malformation/inconsistency), nonempty but
ambiguous (underdetermined), or singleton (identified truth).

## Abstract pattern sought

For each field I looked for the same algebraic signature:

- **Universe** `X`: possible hypotheses, assignments, documents, designs,
  trajectories, models, locations, legal explanations, etc.
- **Property sets** `S_i ⊆ X`: constraints, evidence items, observations,
  rules, criteria, requirements, integrity conditions, habitats, admissibility
  filters, or typicality tests.
- **Feasible remainder** `⋂ᵢ S_i`: the candidates not yet eliminated.
- **Reduction score** `r_i`: a domain-specific estimate of how much a new
  property set should shrink the feasible remainder.
- **Contradiction/malformation**: incompatible property sets produce the empty
  intersection, which should be diagnosed as bad criteria, bad candidate
  generation, bad observations, or model misspecification rather than as a
  successful answer.

I graded each area by how directly it matches crisp STE:

- **A**: essentially the same algebra; usually only terminology differs.
- **B**: strong match, but often probabilistic/weighted/optimization-flavored.
- **C**: useful analogy, but not mainly an intersection-of-hard-property-sets
  method.

## High-confidence isomorphisms or near-isomorphisms

### 1. Constraint satisfaction, SAT, SMT, ASP, and constraint programming — Grade A

**STE fit.** The solution universe is the product of variable domains.  Each
constraint is a relation/property set over assignments.  Solving is finding a
complete assignment in the intersection of all constraints.  Adding constraints
shrinks the feasible assignment set; unsatisfiability is the empty feasible set.

**Reduction score `r`.** In solvers, the practical analogue of `r` is pruning
power: domain wipeout, unit propagation consequences, learnt-clause activity,
branching heuristics, watched-literal effects, or theory-propagation strength.
SAT/CDCL and SMT do not only intersect sets naively; they estimate which choices
or constraints eliminate the most search.

**Contradiction case.** Clause conflict, domain wipeout, or theory conflict is
exactly the disjoint-property-set case.  Conflict analysis then extracts a small
incompatible subset, analogous to finding malformed STE information.

**Sources.** AIMA's CSP chapter defines states/assignments, constraints, legal
assignments, and solutions satisfying all constraints.  The Berkeley CS188 notes
emphasize exponential assignment spaces.  SMT is defined as satisfiability of a
formula with respect to background theories and is used as a back-end in model
checking and verification.  SAT notes describe unit propagation as a way to prune
search space.

- AIMA CSP chapter: https://aima.cs.berkeley.edu/newchap05.pdf
- Berkeley CS188 CSP notes: https://inst.eecs.berkeley.edu/~cs188/textbook/csp/csps.html
- Barrett & Tinelli SMT survey: https://theory.stanford.edu/~barrett/pubs/BT18.pdf
- SAT/unit propagation notes: https://users.aalto.fi/~tjunttil/2020-DP-AUT/notes-sat/solvers.html

**Lean direction.** This is the cleanest next formal analogue after constraint
grammar: encode a CSP as an `STE.Algebra Unit Assignment Constraint`; prove its
solution set is STE feasibility; prove arc/domain filtering is antitone partial
feasibility.

### 2. Version spaces and candidate elimination in machine learning — Grade A

**STE fit.** Mitchell's version-space framework maintains the set of all
hypotheses consistent with observed training examples.  Every positive or
negative example induces a property set of hypotheses.  Candidate elimination is
intersection/refinement of the hypothesis space.

**Reduction score `r`.** A training example's informativeness is the number or
measure of hypotheses it eliminates.  Active learning is therefore a principled
search for high-`r` examples.

**Contradiction case.** Noisy or contradictory examples can collapse the version
space to empty; this is the classic failure mode of crisp candidate elimination.
That is precisely the STE malformation case.

**Sources.** Mitchell's IJCAI paper says the method maintains a space of
plausible rule versions and eliminates versions conflicting with observed
training instances.  Secondary summaries call the maintained set the version
space and describe examples as restrictions of the hypothesis space.

- Mitchell 1977 IJCAI paper: https://www.ijcai.org/Proceedings/77-1/Papers/048.pdf
- Version-space overview: https://en.wikipedia.org/wiki/Version_space_learning

**Lean direction.** `Hypothesis` is the solution type, `Example` the criterion
type, and `consistentWith : Example → Set Hypothesis` the property family.
Active learning can be added later as a reduction-score model.

### 3. Boolean information retrieval and e-discovery search — Grade A/B

**STE fit.** In Boolean retrieval, the universe is a document collection.  A term
posting list is a property set of documents containing that term.  Conjunctive
queries intersect posting lists; NOT subtracts a property set; OR unions.  Legal
e-discovery keyword search uses the same Boolean filtering language to narrow or
exclude documents.

**Reduction score `r`.** Term/document frequency is an explicit reduction
estimate.  A rare term has high shrinkage for AND; high-frequency terms have low
shrinkage.  Query planners exploit posting-list lengths exactly as `r` values.

**Contradiction case.** A conjunction with no hits can mean the query is too
strict, the vocabulary/morphology is malformed, or the target documents are not
in the collection.  In e-discovery, zero or unexpectedly low recall is a legal
process risk, not a truth.

**Sources.** The Stanford IR book introduces term-document matrices, inverted
indexes, and Boolean retrieval.  Legal e-discovery search guides describe AND as
narrowing results and NOT as exclusion.

- Stanford IR Boolean retrieval: https://nlp.stanford.edu/IR-book/html/htmledition/boolean-retrieval-1.html
- e-discovery Boolean search example: https://csdisco.com/blog/ediscovery-search

**Lean direction.** A document-query module would be tiny and useful: documents
as `X`, search clauses as criteria, posting lists as property sets, and query
planning as reduction scoring.

### 4. Database repairs, possible worlds, and consistent query answering — Grade A/B

**STE fit.** The universe is a set of possible database instances/repairs or
possible worlds.  Integrity constraints and observations define admissible
repairs.  Consistent answers are those true across the surviving repaired
versions.

**Reduction score `r`.** Each integrity constraint shrinks the repair space;
query predicates shrink answer-candidate worlds.  Minimal-change repair costs are
weighted versions of reduction.

**Contradiction case.** If no repair exists, constraints and source data are
jointly malformed.  More commonly, multiple repairs remain, giving ambiguity
rather than singleton truth.

**Sources.** Arenas, Bertossi, and Chomicki define consistent answers in terms
of possible repaired versions of an inconsistent relational database.  Later CQA
surveys treat repairs/possible worlds under constraints as the semantic base.

- PODS 1999 paper: https://marceloarenas.cl/publications/pods99.pdf
- Database repairs/CQA survey notes: https://www.cs.ubc.ca/~laks/cpsc504/dc-leo.pdf

**Lean direction.** This is a strong non-crypto application for finite/discrete
topological STE: finite databases, finite repairs, integrity constraints,
intersection semantics, and non-singleton certain-answer logic.

## Physical science and engineering analogues

### 5. Space mission design and trajectory optimization — Grade B

**STE fit.** The universe is mission architectures, launch windows, trajectory
families, control histories, or state/control parameterizations.  Constraints
include launch-window geometry, range safety, aerodynamic loading, propulsion,
orbital insertion, payload, power, thermal, communication, and science-value
requirements.  Feasible mission design is the intersection of all acceptable
regions.

**Reduction score `r`.** Engineering teams already ask which constraints are
most binding: launch windows, C3, declination, delta-v, thermal/power margins,
rendezvous geometry, etc.  A reduction score can be feasibility-volume loss or
optimization sensitivity.

**Contradiction case.** Empty feasibility means no mission design exists under
the stated requirements, often revealing an overconstrained architecture or
incorrect assumptions.  It is not an identified design.

**Sources.** NASA trajectory/mission documents describe launch and boost
trajectories satisfying launch window, range safety, aerodynamic loading, and
orbital insertion constraints.  Recent surveys discuss constrained trajectory
optimization, sequential convex programming, and model predictive control for
space vehicles.

- NASA guidance/trajectory constraints: https://ntrs.nasa.gov/api/citations/19680010999/downloads/19680010999.pdf
- Advances in trajectory optimization: https://arxiv.org/abs/2108.02335
- NASA end-to-end mission design/trajectory optimization: https://ntrs.nasa.gov/citations/20220018523

**Lean direction.** Start symbolically, not numerically: define mission-design
candidate space abstractly and package constraints as property sets; later attach
topological/convex hypotheses to specific continuous constraints.

### 6. Geological reasoning: multiple working hypotheses, equifinality, inverse models — Grade B

**STE fit.** Chamberlin's method of multiple working hypotheses starts with many
possible explanations and uses evidence to eliminate untenable ones.  In
geology, hydrology, and geomorphology, equifinality says many distinct models or
histories may remain acceptable under the observations.  Inverse geophysical
modeling similarly seeks the model set compatible with data and prior bounds.

**Reduction score `r`.** A field observation, stratigraphic relation,
geochemical measurement, or geophysical survey has value proportional to how much
it reduces the admissible hypothesis/model family.

**Contradiction case.** Disjoint evidence constraints can indicate bad dating,
contaminated samples, wrong process model, scale mismatch, or a missing
hypothesis class.

**Sources.** Chamberlin's method explicitly recommends developing multiple
hypotheses before research to avoid fixation on a ruling hypothesis.  Beven's
equifinality work argues for multiple acceptable models in hydrological and
environmental systems.

- Chamberlin multiple working hypotheses: https://www.whoi.edu/cms/files/chamberlin65sci_72744.pdf
- Chamberlin discussion page: https://railsback.org/railsback_chamberlin.html
- Equifinality/uncertainty in geomorphological modeling: https://www.semanticscholar.org/paper/Equifinality-and-Uncertainty-in-Geomorphological-Beven/102098955b3379fb26f47888ad5f3d63ce90dcda

**Lean direction.** This is philosophically close to Holmes.  It suggests a
``multiple hypotheses as STE'' note, with non-singleton feasibility as a first
class conclusion rather than failure.

### 7. Agronomy and environmental-model calibration, including GLUE — Grade B

**STE fit.** The universe is parameter sets for crop, hydrological, or
environmental models.  Observed phenological stages, yield, soil moisture,
tracer data, and management histories impose acceptability criteria.  GLUE-style
methods retain behavioral parameter sets rather than a single optimum.

**Reduction score `r`.** Each dataset or calibration target has shrinkage value:
it excludes parameter combinations.  The best next observation is the one that
most reduces acceptable parameter uncertainty while remaining reliable.

**Contradiction case.** Empty acceptable parameter set suggests model structural
error, bad data, overly strict tolerances, or incompatible calibration targets.

**Sources.** Crop-model calibration studies report GLUE use for parameter
calibration and quantify how observed datasets affect cultivar-specific
parameter estimation.  Recent crop calibration papers describe the difficulty of
parameter estimation and the need for automated frameworks.

- Crop-model GLUE calibration case: https://pmc.ncbi.nlm.nih.gov/articles/PMC11175450/
- DSSAT GLUEP calibration note: https://dssat.net/6021/
- Time-dependent crop parameter estimation: https://www.nature.com/articles/s41598-021-90835-x

**Lean direction.** Formalize `Acceptable : Observation → Set ParameterSet` and
use topological STE when parameter sets are compact and acceptability sets are
closed.

### 8. Marine science, species distribution, and habitat suitability — Grade B

**STE fit.** The universe is spatial cells, 3D ocean volumes, habitat states, or
species-environment models.  Presence/absence records, environmental covariates,
depth, substrate, temperature, oxygen, survey bias filters, and ecological niche
constraints define property sets of plausible locations or models.

**Reduction score `r`.** A covariate layer or survey observation reduces
possible habitat.  High-resolution bathymetry or limiting environmental ranges
can have high reduction value.  In marine settings, dynamic 3D layers and survey
bias mean scores are uncertain.

**Contradiction case.** Disjoint constraints may reveal detection error,
misidentification, temporal mismatch, coarse covariates, or a niche model outside
its transfer domain.

**Sources.** Marine habitat suitability models are used to predict suitable
environmental ranges for species where direct observation is infeasible.  Recent
marine SDM reviews emphasize 3D modeling, temporal resolution, occurrence data,
and bias.

- Marine vulnerable ecosystem habitat suitability: https://academic.oup.com/icesjms/article/78/8/2830/6355116
- Marine SDM trends review page: https://research-portal.st-andrews.ac.uk/en/publications/trends-in-marine-species-distribution-models-a-review-of-methodol/
- NASA remote-sensing SDM training: https://www.earthdata.nasa.gov/s3fs-public/2025-11/SDM_Part1_Final.pdf

**Lean direction.** Treat habitat cells as finite/discrete or compact spatial
spaces; species observations and environmental envelopes are property sets;
uncertain detections push toward probabilistic/fuzzy STE.

### 9. Wildlife management, occupancy models, and conservation planning — Grade B

**STE fit.** For occupancy, the universe is possible occupied site sets or model
parameters.  Detection/non-detection histories and habitat covariates constrain
which occupancy states are plausible.  For reserve planning, the universe is
candidate reserve networks; representation, cost, connectivity, and policy
constraints define property sets.

**Reduction score `r`.** A camera-trap visit, acoustic survey, habitat covariate,
or representation target reduces possible occupancy or reserve designs.  In
systematic conservation planning, the reduction is often optimized against cost.

**Contradiction case.** Impossible reserve targets or occupancy data inconsistent
with detection assumptions indicate infeasible policy requirements or flawed
sampling/model assumptions.

**Sources.** Occupancy models use detection/non-detection data from repeated
visits to estimate species occurrence while accounting for imperfect detection.
Systematic conservation planning defines reserve designs satisfying quantitative
biodiversity objectives at minimum cost.

- Occupancy model covariate paper: https://www.nature.com/articles/srep17041
- Occupancy model management example: https://nri.tamu.edu/publications/peer-reviewed-publications/2012/utilization-of-a-species-occupancy-model-for-management-and-conservation/
- Marxan systematic conservation planning framework: https://marxansolutions.org/a-framework-for-systematic-conservation-planning/
- Marxan with Zones conservation objective PDF: https://dusk.geo.orst.edu/Pickup/marxan_w_zones.pdf

**Lean direction.** Reserve selection is almost literally finite STE with an
optimization layer: first intersect hard acceptability property sets, then rank
feasible networks by cost.

## Information, computation, and verification analogues

### 10. Model checking and formal verification — Grade B

**STE fit.** The universe is reachable states, executions, traces, or models of a
system.  Temporal-logic properties and safety assertions filter traces/states.
Counterexample generation finds a witness in the bad-property feasible set;
proof shows that set is empty.

**Reduction score `r`.** State-space reduction, abstraction refinement,
interpolation, and symbolic representations estimate which predicates/properties
most reduce the search.

**Contradiction case.** If a specification set and implementation-reachable set
are disjoint, either the system is verified against a forbidden behavior or the
requirements are inconsistent.  If expected behavior is eliminated, the model or
spec is malformed.

**Sources.** Model-checking texts describe temporal properties over paths and
the state-explosion problem; SMT surveys note SMT solvers as back-end engines
for bounded, interpolation-based, and predicate-abstraction model checking.

- Model checking/state explosion: https://pzuliani.github.io/papers/LASER2011-Model-Checking.pdf
- SMT and model checking: https://theory.stanford.edu/~barrett/pubs/BT18.pdf

**Lean direction.** `Trace` as solution universe; each temporal property as a
property set.  This may connect to topology via closed trace languages or safety
properties as prefix-closed sets.

### 11. Abstract interpretation and static analysis — Grade C/B

**STE fit.** Abstract interpretation is usually over-approximation rather than
candidate elimination.  However, invariant inference can be read dually: compute
an abstract set of possible program states and refine it by transfer functions,
guards, and assertions.  The lattice/fixpoint structure is central.

**Reduction score `r`.** Narrowing, guard filtering, relational domains, and
predicate refinement reduce abstract state sets.  Widening intentionally loses
precision, so this is not pure monotone shrinking.

**Contradiction case.** Empty abstract state can mean unreachable code,
impossible assertion context, or over-strong assumptions.

**Sources.** Cousot and Cousot describe abstract interpretation as describing
program computations in another universe of abstract objects; the classic model
is lattice-theoretic fixpoint approximation.

- Cousot & Cousot POPL 1977 page: https://www.di.ens.fr/~cousot/COUSOTpapers/POPL77.shtml
- Abstract interpretation summary: https://homes.cs.washington.edu/~rjust/courses/CSEP504/ai_summary.pdf

**Lean direction.** Useful but not the first target.  It requires a dual story:
over-approximating possible executions, then meeting with assertions/guards.

### 12. Type inference and program synthesis — Grade A/B

**STE fit.** Candidate types/programs inhabit a search universe.  Constraints
from usage sites, examples, specifications, and tests carve out the consistent
candidates.  Program synthesis from examples is version-space learning over
programs.

**Reduction score `r`.** A test/example/spec clause is valuable if it eliminates
many candidate programs.  Counterexample-guided inductive synthesis (CEGIS)
uses generated counterexamples precisely as high-value property sets.

**Contradiction case.** Unsatisfiable type constraints or no program satisfying
examples indicates inconsistent annotations/examples/specs or an insufficient
language bias.

**Sources.** SMT sources explicitly list type inference, synthesis, symbolic
execution, and software testing among SMT applications.

- SMT applications overview: https://en.wikipedia.org/wiki/Satisfiability_modulo_theories
- Barrett & Tinelli SMT survey: https://theory.stanford.edu/~barrett/pubs/BT18.pdf

**Lean direction.** Good bridge to theorem proving: candidate proof/program
terms as universe, typing/specification constraints as property sets.

## Legal and evidentiary analogues

### 13. Legal fact-finding, inference to best explanation, and reasonable doubt — Grade C/B

**STE fit.** The universe is possible factual narratives or explanations.  Each
admissible evidence item and legal rule eliminates narratives inconsistent with
it.  Inference to best explanation then ranks the remaining narratives; proof
beyond a reasonable doubt demands strong elimination of reasonable alternatives.

**Reduction score `r`.** Evidence value is partly its ability to eliminate
competing explanations.  However, legal relevance, admissibility, burdens, and
standards of proof make this a weighted/normative analogue rather than crisp
STE.

**Contradiction case.** Inconsistent evidence can reflect perjury, faulty memory,
chain-of-custody problems, inadmissible evidence, or an incomplete narrative
space.  Empty intersection is not guilt; it is a failure of the evidentiary model.

**Sources.** Pardo and Allen argue that inference to the best explanation helps
explain proof at trial.  Cornell's Wex describes beyond a reasonable doubt as the
criminal standard requiring jurors to be firmly convinced.  E-discovery sources
show Boolean narrowing/exclusion in legal document search.

- Pardo & Allen juridical proof/IBE: https://sites.pitt.edu/~jdnorton/teaching/2682_confirmation/2021/slides/evidence_in_science/Pardo_Allen_2007.pdf
- Cornell Wex reasonable doubt: https://www.law.cornell.edu/wex/beyond_a_reasonable_doubt
- E-discovery Boolean search: https://csdisco.com/blog/ediscovery-search

**Lean direction.** Treat with caution.  Crisp STE can model admissible hard
exclusions, but legal proof also needs weights, standards, narrative coherence,
and institutional rules.

## Cross-domain synthesis

### 14. The general taxonomy

The strongest STE analogues fall into four families:

1. **Exact finite/discrete feasibility**: CSP, SAT, SMT fragments, Boolean IR,
   database repairs, reserve selection.  These are immediate targets for Lean.
2. **Hypothesis-space elimination**: version spaces, multiple working
   hypotheses, legal/explanatory reasoning, diagnosis.  These match Holmes most
   directly.
3. **Continuous/topological feasibility**: trajectory design, inverse problems,
   crop/hydrological calibration, habitat suitability.  These motivate compact,
   closed, convex, and measure/probability extensions.
4. **Approximate/weighted feasibility**: GLUE, Bayesian calibration, legal proof,
   IR ranking, species distribution models.  These require scores, likelihoods,
   fuzzy sets, or acceptability thresholds layered on top of crisp STE.

### 15. Reduction score `r` as the unifying engineering layer

Across fields, the practical question is not merely whether `S_i` is a property
set.  It is whether `S_i` is worth applying next.  The recurring scoring
families are:

- **Cardinality reduction**: how many finite candidates are removed?
- **Measure/volume reduction**: how much feasible volume is cut away?
- **Entropy/information reduction**: how many bits of uncertainty are removed?
- **Expected value of information**: how much will an observation reduce future
  ambiguity in expectation?
- **Computational pruning**: how much search-tree branching is avoided?
- **Cost-adjusted reduction**: how much shrinkage per dollar, field hour,
  spacecraft mass, survey day, or legal-review hour?

Carlson's AEP use belongs in the entropy/typicality row.  It estimates which
meaningfulness/typicality property sets should collapse the feasible key/message
space rapidly while preserving the true plaintext.

### 16. Contradiction is a first-class outcome

Nearly every analogue has a native name for `⋂ᵢ S_i = ∅`:

- SAT/SMT/CSP: unsatisfiable, conflict, domain wipeout.
- Version spaces: empty version space from noise or inconsistent examples.
- Database repairs: no repair, inconsistent constraints.
- Mission design: infeasible architecture/trajectory.
- Geology/environmental modeling: model-data mismatch or missing hypothesis.
- Crop calibration: no behavioral parameter set.
- Habitat/occupancy: survey/model/covariate mismatch.
- Legal proof: inconsistent evidence or impossible narrative set.

This supports adding contradiction diagnostics to STE rather than treating
emptiness as merely a negative result.

## Recommended next research notes

1. **CSP/SAT/SMT as STE**: likely highest-value mechanized note after CG.
2. **Version spaces as STE**: closest to Holmes and conceptually clean.
3. **Database repairs / possible worlds as STE**: excellent finite-discrete
   topological application.
4. **Multiple working hypotheses and equifinality as STE**: strong scientific
   philosophy note linking geology/hydrology to non-singleton feasibility.
5. **Reduction score taxonomy**: a theory note connecting `Ste.Reduction` to
   cardinality, measure, entropy, and cost-adjusted value of information.
6. **Reserve selection / conservation planning as finite STE plus optimization**:
   useful bridge to wildlife/marine/agronomy applications.

## Bottom line

The STE pattern is far broader than the literatures that name STE.  The common
algebra is: construct a possibility universe, interpret information as property
sets, repeatedly meet/intersect those property sets, and inspect the remainder.
The project should therefore position STE as a unifying formal language for
Holmesian elimination across AI, databases, scientific inverse problems,
mission design, ecological management, legal reasoning, and information search.
