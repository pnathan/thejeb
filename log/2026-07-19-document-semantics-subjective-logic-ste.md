# Document semantics, subjective logic, and STE truth reduction

Date: 2026-07-19

User prompt: a document collection can contain many semantic or subjective
``hyper-claims'' across many documents; the task is to reduce the space of
possible truths by applying those claims as evidence/property sets.

## Assessment

This is strongly aligned with STE, but it is usually named differently in the
literature:

- **Truth discovery / truth finding / data fusion**: infer true values from
  multiple noisy, conflicting sources.
- **Knowledge graph conflict resolution**: reconcile conflicting triples or
  object-property-value claims.
- **Subjective logic / opinion fusion**: represent belief, disbelief, and
  uncertainty about propositions and combine opinions from sources, often with
  trust discounting.
- **Semantic document analysis**: extract typed claims from text and reason over
  their compatibility using schemas, ontologies, provenance, and source trust.

The STE structure is:

- **Universe `X`**: candidate worlds, candidate fact assignments, candidate
  knowledge graphs, candidate truth-value assignments to propositions, or
  candidate semantic interpretations of a corpus.
- **Criteria/property sets `S_i`**: each extracted claim, source assertion,
  ontology rule, provenance rule, credibility condition, temporal constraint, or
  subjective opinion threshold induces the set of worlds/graphs/truth assignments
  compatible with it.
- **Feasible truth remainder**: `⋂ᵢ S_i`, the worlds not eliminated by the
  accepted evidence and semantic constraints.
- **Reduction score `r`**: expected reduction in candidate worlds, entropy loss,
  source-reliability-weighted exclusion, or subjective-logic uncertainty
  reduction.
- **Contradiction**: disjoint claims/constraints yield empty feasibility, which
  indicates conflicting documents, extraction error, source unreliability,
  ontology/schema mismatch, temporal mismatch, or a missing candidate-world model.

## Truth discovery is the closest named literature

Truth discovery is almost the database/document-collection name for this problem.
The standard setup is that sources provide conflicting claims about objects, and
the algorithm jointly estimates source reliability and true values.  This is a
weighted or probabilistic version of STE:

- A claim such as `(object=o, attribute=a, value=v)` defines a property set of
  candidate truth assignments where `a(o)=v`.
- Multiple mutually exclusive values for the same slot define disjoint property
  sets unless the model allows multi-truth.
- Source reliability changes the score/weight of a property set rather than the
  underlying set-theoretic semantics.
- Copying/dependence between sources changes the effective reduction score `r`,
  because repeated dependent claims should not be counted as independent
  evidence.

Key sources found:

- Li et al., **A Survey on Truth Discovery**: frames truth discovery as resolving
  conflicts among multi-source noisy information and inferring source reliability
  together with truths.  URL: https://www.kdd.org/exploration_files/Article1_17_2.pdf
- Yin, Han, and Yu, **Truth Discovery with Multiple Conflicting Information
  Providers on the Web**: early TruthFinder work on conflicting web information.
  URL: https://experts.illinois.edu/en/publications/truth-discovery-with-multiple-conflicting-information-providers-o-2/
- Dong, Berti-Equille, and Srivastava, **Data Fusion: Resolving Conflicts from
  Multiple Sources**: emphasizes source dependence/copying while resolving
  conflicts.  URL: https://research.google/pubs/data-fusion-resolving-conflicts-from-multiple-sources/
- Domain-aware multi-truth discovery: distinguishes single-truth from multi-truth
  settings, important because not all conflicting claims are logically exclusive.
  URL: https://www.vldb.org/pvldb/vol11/p635-lin.pdf

## Subjective logic adds a graded belief layer over STE

Subjective logic represents opinions with belief, disbelief, uncertainty, and
base rates.  It is not crisp STE by itself, because opinions do not necessarily
eliminate candidates absolutely.  But it fits naturally as a scoring/relaxation
layer over the STE algebra:

- A binomial opinion on proposition `P` can be converted to a soft criterion on
  candidate worlds: worlds satisfying `P` receive belief support; worlds
  violating `P` receive disbelief support; uncertainty preserves multiple
  candidates.
- A hard threshold such as ``accept claims with belief above τ and uncertainty
  below υ'' turns subjective opinions into crisp property sets.
- Discounting by source trust changes a claim's reduction score `r` before it is
  allowed to shrink the feasible set.
- Consensus/fusion operators combine several opinions about the same proposition;
  in STE terms, this determines whether the resulting criterion is fair,
  contradictory, weak, or high-reduction.

Key sources found:

- Jøsang, **Subjective Logic: A Formalism for Reasoning Under Uncertainty**:
  subjective logic combines logic/probability and represents uncertainty
  explicitly.  URL: https://link.springer.com/book/10.1007/978-3-319-42337-1
- Jøsang subjective-logic tutorial slides: opinions, evidence, trust networks,
  deduction/abduction, and subjective Bayesian reasoning.  URL:
  https://www.mn.uio.no/ifi/english/people/aca/josang/sl/subjective-logic-fusion-2022.pdf
- Evidence-based discounting rule in subjective logic: discusses consensus and
  discounting as important operations for combining opinions.  URL:
  https://scispace.com/pdf/evidence-based-discounting-rule-in-subjective-logic-4c4u2n6d3c.pdf

## Semantic document collections as candidate-world STE

For a document collection, a practical STE model can be staged:

1. **Extraction stage**: convert text spans into normalized claims/triples,
   retaining provenance and confidence.
2. **Universe construction**: define candidate worlds/knowledge graphs assigning
   values, relations, temporal intervals, and provenance statuses.
3. **Semantic property sets**: ontology/domain rules, type constraints,
   uniqueness constraints, temporal consistency, source assertions, and subjective
   opinions define subsets of candidate worlds.
4. **Reduction and ranking**: apply crisp high-confidence constraints first;
   use subjective-logic or truth-discovery scores to prioritize high-value,
   high-trust reductions.
5. **Outcome taxonomy**:
   - empty feasible set: inconsistent corpus/model/extraction;
   - multiple worlds: ambiguity or underdetermination;
   - singleton world: STE ideal truth identification;
   - weighted feasible set: probabilistic/subjective ranking of remaining worlds.

This is very close to Holmes' dictum, but with an important caveat: in document
collections, ``whatever remains'' is often not a single truth.  It may be a
ranked set of feasible worlds, a credal set, or several partially true values.
The STE contribution is to separate the hard eliminative layer from the graded
belief/trust layer.

## Relation to existing STE modules

- `Ste.Algebra`: candidate worlds are `Solution`; documents/claims/rules are
  `Criterion`; the claim interpretation is `propertySet`.
- `Ste.Reduction`: a claim's exact crisp reduction is `reductionSet`; its
  subjective/trust/truth-discovery priority is a `ReductionScore`.
- `Ste.Topology`: finite document collections and finite candidate worlds fit the
  finite/discrete story; richer semantic spaces may motivate compactness or
  closure assumptions.
- Future fuzzy/probabilistic STE: subjective logic is a prime candidate for the
  first weighted/uncertain extension.

## Recommended follow-up note

Create a dedicated note tentatively titled **Semantic Truth Discovery as STE**.
The core theorem should not be that truth discovery algorithms are identical to
STE; rather:

> The hard semantic consistency layer of document-level truth discovery is an
> STE problem over candidate worlds, while source reliability and subjective
> logic provide reduction scores or fuzzy relaxations over that feasibility
> algebra.

Possible Lean skeleton:

```lean
structure ClaimWorldAlgebra (World Claim : Type*) where
  propertySet : Claim → Set World
  score : Claim → Score -- optional later layer
```

But this should probably reuse `STE.Algebra Unit World Claim` rather than create
another new structure.
