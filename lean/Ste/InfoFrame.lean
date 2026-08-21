/-
Information frames: the single antitone-descent theorem behind every
STE "more evidence shrinks the answer set" corollary.

Across the development the same argument is repeated once per domain:

* `Ste.Algebra`         — more criteria, fewer admissible solutions;
* `Ste.ConstraintGrammar` — more hard rules, fewer surviving parses;
* `Ste.DynamicFrame`    — more documents, fewer feasible normalizations.

In each case the data is the same triple: an *evidence* type whose
subsets are accumulated, an *activation* map sending an evidence set to
the constraints it switches on (monotone: evidence is never retracted),
and an *interpretation* map sending a constraint to the set of
hypotheses it admits.  The feasible set is then
`partialFeasibilitySet` of the interpretation over the activated
constraints, and antitonicity is the composite of `act_mono` with
`STE.partialFeasibilitySet_antitone`.

`InfoFrame` packages that triple, and `InfoFrame.feasible_antitone` is
the one theorem; the per-domain statements are instantiations.

Beyond antitonicity, two descent facts:

* `feasible_iUnion` — feasibility turns unions of evidence into
  intersections of feasible sets.  This needs the activation map to be
  *continuous* (`act (⋃ k, D k) = ⋃ k, act (D k)`), which monotonicity
  alone does not give; without it only the inclusion
  `feasible_iUnion_subset` survives.
* `eventually_stable` — over a finite hypothesis space, a monotone
  stream of evidence stabilizes: past some stage the feasible set is
  already the limit feasible set (`STE.antitone_eventually_eq_iInter`).

## On the `sInf` characterizations (U4)

Three results in this development characterize a forced coreference
relation as an `sInf` in the complete lattice `Setoid _`:
`STE.Coreference.forcedCoref_eq_sInf`,
`STE.FrameCoref.posSetoid_eq_sInf`, and
`STE.DynamicFrame.Model.mustSetoid_eq_sInf`.  No abstraction is offered
here for them, deliberately.  The first two share a real common shape,
but that shape is already a Mathlib lemma: the constructed object is the
*least* element of the set of "adequate" relations, so
`IsLeast.isGLB` / `IsGLB.sInf_eq` is the whole content, and any wrapper
would only rename it.  The third is a different fact — an `sInf` of an
*image* family unfolded pointwise by `Setoid.sInf_iff` — and does not
share that shape at all.  See the docstrings at the three theorems.
-/
import Ste.Sheaf

namespace STE

/-- An **information frame**: documents (evidence) activate constraints,
and constraints carve the hypothesis space `Ξ`.

* `act` sends an evidence set to the constraints it switches on;
* `act_mono` says evidence is never retracted — a larger corpus
  activates at least the same constraints;
* `prop` interprets each constraint as its property set of admissible
  hypotheses (Combettes 1993, §II-C, Eq. (3)). -/
structure InfoFrame (Doc K Ξ : Type*) where
  /-- The constraints activated by a set of documents. -/
  act : Set Doc → Set K
  /-- Evidence is never retracted: activation is monotone. -/
  act_mono : Monotone act
  /-- The property set of hypotheses admitted by a constraint. -/
  prop : K → Set Ξ

namespace InfoFrame

variable {Doc K Ξ : Type*} (F : InfoFrame Doc K Ξ)

/-- The hypotheses admitted by every constraint the corpus `D` activates:
the partial feasibility set over the activated constraints. -/
def feasible (D : Set Doc) : Set Ξ :=
  STE.partialFeasibilitySet F.prop (F.act D)

theorem mem_feasible {D : Set Doc} {a : Ξ} :
    a ∈ F.feasible D ↔ ∀ k ∈ F.act D, a ∈ F.prop k := by
  simp [feasible, STE.partialFeasibilitySet]

/-- **Information monotonicity, once and for all.**  Acquiring more
documents activates more constraints and can only shrink the feasible
set.  Every per-domain antitonicity corollary in this development is an
instance of this theorem. -/
theorem feasible_antitone : Antitone F.feasible :=
  fun _ _ hDE => STE.partialFeasibilitySet_antitone F.prop (F.act_mono hDE)

/-- The always-available half of descent: the feasible set of a union of
corpora refines each local feasible set, hence their intersection.  Needs
no continuity of `act` — only `act_mono`, via `feasible_antitone`. -/
theorem feasible_iUnion_subset {κ : Type*} (D : κ → Set Doc) :
    F.feasible (⋃ k, D k) ⊆ ⋂ k, F.feasible (D k) :=
  Set.subset_iInter fun k => F.feasible_antitone (Set.subset_iUnion D k)

/-- **Descent along a union of corpora.**  If activation is continuous —
the constraints activated by a union of corpora are exactly those
activated by some member — then feasibility takes unions of evidence to
intersections of feasible sets.  This is
`STE.partialFeasibilitySet_iUnion` (the constraint-side sheaf condition
of `Ste.Sheaf`) transported along `act`.

Continuity is a genuine hypothesis: `act_mono` alone gives only
`feasible_iUnion_subset`. -/
theorem feasible_iUnion {κ : Type*} (D : κ → Set Doc)
    (hact : F.act (⋃ k, D k) = ⋃ k, F.act (D k)) :
    F.feasible (⋃ k, D k) = ⋂ k, F.feasible (D k) := by
  simp only [feasible, hact]
  exact STE.partialFeasibilitySet_iUnion F.prop _

/-- **Eventual stability of a monotone evidence stream.**  Over a finite
hypothesis space, an increasing corpus `D 0 ⊆ D 1 ⊆ ⋯` cannot keep
shrinking the feasible set forever: past some stage the feasible set is
already the intersection of all of them.  Order-theoretic content:
`STE.antitone_eventually_eq_iInter` applied to `F.feasible ∘ D`. -/
theorem eventually_eq_iInter [Finite Ξ] (D : ℕ → Set Doc) (hD : Monotone D) :
    ∀ᶠ n in Filter.atTop, F.feasible (D n) = ⋂ i, F.feasible (D i) :=
  STE.antitone_eventually_eq_iInter (F.feasible_antitone.comp_monotone hD)

/-- **Eventual stability against the limit corpus.**  With continuous
activation, the stable value of `eventually_eq_iInter` is the feasible
set of the whole (limit) corpus: finitely many documents already
determine the answer. -/
theorem eventually_stable [Finite Ξ] (D : ℕ → Set Doc) (hD : Monotone D)
    (hact : F.act (⋃ n, D n) = ⋃ n, F.act (D n)) :
    ∀ᶠ n in Filter.atTop, F.feasible (D n) = F.feasible (⋃ n, D n) := by
  have hlim : F.feasible (⋃ n, D n) = ⋂ i, F.feasible (D i) :=
    F.feasible_iUnion D hact
  filter_upwards [F.eventually_eq_iInter D hD] with n hn
  rw [hn, hlim]

/-! ### The tautological frame

Every family of property sets is an information frame in which the
"documents" are the constraints themselves and activation is the
identity.  This is the bridge used by `Ste.Algebra` and
`Ste.ConstraintGrammar`, where evidence accumulation *is* constraint
accumulation. -/

/-- The information frame of a bare property-set family: documents are
constraints, activation is the identity. -/
def ofProperties {I : Type*} (S : I → Set Ξ) : InfoFrame I I Ξ where
  act := id
  act_mono := monotone_id
  prop := S

@[simp] theorem ofProperties_feasible {I : Type*} (S : I → Set Ξ) (J : Set I) :
    (ofProperties S).feasible J = STE.partialFeasibilitySet S J :=
  rfl

end InfoFrame

end STE
