/-
Multidocument coreference over HYPERCLAIMS: claims whose determinate
reading is unresolved.

`Ste.FrameCoref` treats a document as a determinate bundle of positive
and negative coreference evidence, with property set `propertySet d` and
corpus feasibility `multidocFeasibility docs`.  Extraction, however, is
not always determinate: a sentence under interpretive dispute, an
ambiguous anaphor, or a candidate normalization offers *several*
readings, and the text commits only to their disjunction.  This file
mechanizes that layer.

**The reading.**  A `HyperClaim` is a nonempty set of `Document F`s --- its
readings.  Its information is the union of the readings' property sets
(`hyperPropertySet`), so a coreference state satisfies the claim as soon
as it satisfies SOME reading.  This is exactly the crisp/possibilistic
specialization of a Jøsang hyperopinion (belief mass on a handful of
subsets, vacuous base rate) worked out in
`papers/notes/hyperopinions_ste_feasible_sets.md`, and it is the
`Ste.PluralFeasibility` hyper source `H : ι → Set (Set Ξ)` instantiated
at `Ξ := Setoid F`, `ι := ↥C`, `H c := propertySet '' c.readings`.

**Lazy vs. branch semantics.**  `hyperFeasibility C` is the *lazy*
semantics: intersect the per-claim unions and never enumerate anything.
`hyperFeasibility_eq_iUnion_choice` is the *branch* semantics: the same
set is the union, over all selections of one reading per claim, of the
ordinary `multidocFeasibility` of the selected documents.  The identity
is complete distributivity of `⋂` over `⋃` --- the frame-coreference
instance of
`STE.PluralFeasibility.iInter_hyperInfo_eq_iUnion_choice` --- and in
general it consumes the Axiom of Choice (a choice function per claim).

**The blow-up.**  Branch semantics enumerates `∏_{c ∈ C} |c.readings|`
corpora.  That product is the honest cost of eagerness, and it is the
same phenomenon `Ste.RepresentationBounds` measures for constraint
representations: `rectCoverNumber_le_encard` bounds a rectangle cover by
the whole set, and `exists_cechObstruction_lt_rectCoverNumber` shows
there is no cheap local certificate forcing the count down.  Lazy
semantics is therefore the preferred implementation; branch semantics is
the *specification*.

**Removal is not invertible.**  Insertion of a claim intersects
branchwise and discards empty branches; that discard is non-injective,
so deleting a claim cannot be replayed backwards --- it requires
recomputation from the surviving claims.  `hyperFeasibility_antitone`
records only the monotone half.

**Entity layer.**  `mergeCompatible` and `entityFeasibility` attach a
set-valued attribute map `attr : F → Set W` (the `Ste.SetValuedFrame`
possibility-set reading) to the merged clusters and demand that every
cluster's attribute possibilities intersect.  This discharges the
frame-level half of the monograph's Chapter 9 open item (iii),
"entity-level frames --- attaching set-valued frames to merged clusters
and asking when the merged frame remains feasible":
`mergeCompatible_of_le` gives the order behaviour and
`entityFeasibility_nonempty_of_posSetoid` gives the bottom witness.

## Honest boundary --- what is NOT proved here

* **Interacting readings.**  Readings are selected independently, one
  per claim.  A corpus where choosing reading `r` of claim `c` *forces*
  reading `r'` of claim `c'` (agreement of anaphoric chains across a
  discourse) is not expressible: `hyperFeasibility` quantifies over the
  full product of readings, with no cross-claim constraint.
* **Second-order selection.**  `Ste.Carlson.SetOfSets` studies the
  genuinely second-order question --- whether `k`-wise *selectable*
  consistency certifies global selectability --- and answers no
  (`exists_not_hasHellySel_two`).  Nothing here upgrades that: we do not
  prove any Helly-type locality principle for hyperclaims, and by the
  `SetOfSets` counterexample none of Helly number 2 is available.
* **Grading.**  Readings are unweighted.  A hyperopinion with a genuine
  belief-mass assignment over branches, and the fuzzy lift of
  `Ste.FuzzyFrame`, are out of scope; the whole file is crisp.
* **Removal / retraction.**  Only the antitone half is proved; no
  inverse update law is claimed (see above).
* **Entity layer is frame-level only.**  `mergeCompatible` asks for
  nonempty attribute intersection per cluster.  It says nothing about
  gluing merged frames over a cover, nor about the cohomological
  obstruction of `Ste.CechObstruction` for the merged system --- the
  remaining half of open item (iii).
-/
import Ste.FrameCoref
import Ste.PluralFeasibility

namespace STE.HyperCoref

open STE.FrameCoref

variable {F W : Type*}

/-! ## Hyperclaims -/

/-- A *hyperclaim*: a claim from a text whose determinate reading is
unresolved.  Each reading is an ordinary `Document F`, and the claim
commits only to the disjunction of its readings. -/
structure HyperClaim (F : Type*) where
  /-- The alternative determinate readings of the claim. -/
  readings : Set (Document F)
  /-- A claim offers at least one reading. -/
  nonempty : readings.Nonempty

/-- The information carried by a hyperclaim: a coreference state
satisfies the claim as soon as it satisfies SOME reading. -/
def hyperPropertySet (c : HyperClaim F) : Set (Setoid F) :=
  ⋃ d ∈ c.readings, propertySet d

/-- The hyperclaim feasibility set of a corpus: the lazy semantics,
intersecting the per-claim unions without enumerating branches. -/
def hyperFeasibility (C : Set (HyperClaim F)) : Set (Setoid F) :=
  ⋂ c ∈ C, hyperPropertySet c

/-- Membership in the hyperclaim feasibility set, unfolded. -/
theorem mem_hyperFeasibility {C : Set (HyperClaim F)} {R : Setoid F} :
    R ∈ hyperFeasibility C ↔ ∀ c ∈ C, ∃ d ∈ c.readings, R ∈ propertySet d := by
  simp only [hyperFeasibility, hyperPropertySet, Set.mem_iInter, Set.mem_iUnion,
    exists_prop]

/-- **Information monotonicity for hyperclaims**: acquiring more claims
can only shrink the feasibility set.  The hyper analogue of
`STE.FrameCoref.feasibility_antitone`. -/
theorem hyperFeasibility_antitone {C C' : Set (HyperClaim F)} (h : C ⊆ C') :
    hyperFeasibility C' ⊆ hyperFeasibility C := by
  intro R hR
  rw [mem_hyperFeasibility] at hR ⊢
  exact fun c hc => hR c (h hc)

/-- Pooling two hyper corpora intersects their feasibility sets. -/
theorem hyperFeasibility_union (C C' : Set (HyperClaim F)) :
    hyperFeasibility (C ∪ C') = hyperFeasibility C ∩ hyperFeasibility C' := by
  simp only [hyperFeasibility, Set.biInter_union]

/-! ## Branch semantics = lazy semantics

The distributivity identity.  A *selection* for a corpus `C` is a
function choosing one reading of each active claim; the branch semantics
is the union over selections of the ordinary corpus feasibility set of
the selected documents. -/

/-- A selection of one reading per active hyperclaim. -/
abbrev Selection (C : Set (HyperClaim F)) : Type _ :=
  ∀ c : C, {d : Document F // d ∈ (c : HyperClaim F).readings}

/-- The determinate corpus picked out by a selection. -/
def selected {C : Set (HyperClaim F)} (σ : Selection C) : Set (Document F) :=
  Set.range fun c => (σ c).1

/-- **Branch decomposition of hyperclaim feasibility.**  The lazy
semantics agrees with the branch semantics: intersecting the per-claim
unions is the same as taking the union, over all selections of one
reading per claim, of the ordinary `multidocFeasibility` of the selected
documents.  This is complete distributivity of `⋂` over `⋃`, i.e. the
frame-coreference instance of
`STE.PluralFeasibility.iInter_hyperInfo_eq_iUnion_choice`; it uses
choice. -/
theorem hyperFeasibility_eq_iUnion_choice (C : Set (HyperClaim F)) :
    hyperFeasibility C = ⋃ σ : Selection C, multidocFeasibility (selected σ) := by
  ext R
  simp only [Set.mem_iUnion]
  constructor
  · intro hR
    rw [mem_hyperFeasibility] at hR
    have hR' : ∀ c : C, ∃ d ∈ (c : HyperClaim F).readings, R ∈ propertySet d :=
      fun c => hR c c.2
    choose d hd hRd using hR'
    refine ⟨fun c => ⟨d c, hd c⟩, ?_⟩
    rw [mem_multidocFeasibility]
    rintro e ⟨c, rfl⟩
    exact hRd c
  · rintro ⟨σ, hσ⟩
    rw [mem_multidocFeasibility] at hσ
    rw [mem_hyperFeasibility]
    intro c hc
    exact ⟨(σ ⟨c, hc⟩).1, (σ ⟨c, hc⟩).2, hσ _ ⟨⟨c, hc⟩, rfl⟩⟩

/-! ## The degenerate (determinate) case

A hyperclaim with a single reading is an ordinary document, and a corpus
of such claims is an ordinary corpus: `Ste.FrameCoref` embeds. -/

/-- The determinate hyperclaim with the single reading `d`. -/
def ofDocument (d : Document F) : HyperClaim F :=
  ⟨{d}, ⟨d, rfl⟩⟩

/-- A single-reading hyperclaim carries exactly its reading's
information. -/
@[simp] theorem hyperPropertySet_ofDocument (d : Document F) :
    hyperPropertySet (ofDocument d) = propertySet d := by
  simp [hyperPropertySet, ofDocument]

/-- **`Ste.FrameCoref` is the determinate special case.**  A corpus of
single-reading hyperclaims has exactly the ordinary multidocument
feasibility set of the underlying documents. -/
theorem hyperFeasibility_image_ofDocument (docs : Set (Document F)) :
    hyperFeasibility (ofDocument '' docs) = multidocFeasibility docs := by
  ext R
  rw [mem_hyperFeasibility, mem_multidocFeasibility]
  constructor
  · intro h d hd
    obtain ⟨e, he, hRe⟩ := h (ofDocument d) ⟨d, hd, rfl⟩
    simp only [ofDocument, Set.mem_singleton_iff] at he
    exact he ▸ hRe
  · rintro h c ⟨d, hd, rfl⟩
    exact ⟨d, rfl, h d hd⟩

/-! ## Nonemptiness: coherence of a hyper corpus -/

/-- A hyper corpus is coherent exactly when SOME selection of readings
yields a coherent determinate corpus. -/
theorem hyperFeasibility_nonempty_iff (C : Set (HyperClaim F)) :
    (hyperFeasibility C).Nonempty ↔
      ∃ σ : Selection C, (multidocFeasibility (selected σ)).Nonempty := by
  rw [hyperFeasibility_eq_iUnion_choice, Set.nonempty_iUnion]

/-- **Coherence criterion for hyperclaims.**  A hyper corpus is coherent
exactly when some choice of one reading per claim leaves no forbidden
pair inside a positive component --- the hyper lift of
`STE.FrameCoref.multidocFeasibility_nonempty_iff`. -/
theorem hyperFeasibility_nonempty_iff_no_forced_negative (C : Set (HyperClaim F)) :
    (hyperFeasibility C).Nonempty ↔
      ∃ σ : Selection C, ∀ d ∈ selected σ, ∀ e ∈ d.negative_edges,
        ¬ posSetoid (selected σ) e.1 e.2 := by
  rw [hyperFeasibility_nonempty_iff]
  exact exists_congr fun σ => multidocFeasibility_nonempty_iff (selected σ)

/-! ## The entity layer: merge-activated frame unification

Merging frames into a cluster only makes sense if the cluster's
attribute possibilities (a `Ste.SetValuedFrame`-style possibility set per
frame) still have a common value.  This is the frame-level half of
monograph Chapter 9 open item (iii). -/

/-- A coreference state is *merge compatible* with an attribute map when
every cluster's attribute possibility sets have a common value: merging
never forces an attribute contradiction. -/
def mergeCompatible (attr : F → Set W) (R : Setoid F) : Prop :=
  ∀ f : F, (⋂ g ∈ {g | R g f}, attr g).Nonempty

/-- Entity-level feasibility: coreference states that satisfy every
hyperclaim AND unify attributes across every merged cluster. -/
def entityFeasibility (C : Set (HyperClaim F)) (attr : F → Set W) : Set (Setoid F) :=
  hyperFeasibility C ∩ {R | mergeCompatible attr R}

/-- **Merge compatibility passes to refinements.**  In Mathlib's order on
`Setoid`, `R ≤ R'` means `R`'s classes refine `R'`'s, so the coarser `R'`
merges more frames and intersects more possibility sets.  Compatibility
of the coarser state therefore implies compatibility of the finer one;
the converse direction is false in general (splitting is always safe,
merging is not). -/
theorem mergeCompatible_of_le {attr : F → Set W} {R R' : Setoid F} (h : R ≤ R')
    (hR' : mergeCompatible attr R') : mergeCompatible attr R := by
  intro f
  obtain ⟨w, hw⟩ := hR' f
  exact ⟨w, Set.mem_iInter₂.mpr fun g hg =>
    Set.mem_iInter₂.mp hw g (Setoid.le_def.mp h hg)⟩

/-- Membership in the entity feasibility set, unfolded. -/
theorem mem_entityFeasibility {C : Set (HyperClaim F)} {attr : F → Set W}
    {R : Setoid F} :
    R ∈ entityFeasibility C attr ↔ R ∈ hyperFeasibility C ∧ mergeCompatible attr R :=
  Iff.rfl

/-- Entity-level feasibility is antitone in the corpus, exactly as the
frame-level one. -/
theorem entityFeasibility_antitone {C C' : Set (HyperClaim F)} (attr : F → Set W)
    (h : C ⊆ C') : entityFeasibility C' attr ⊆ entityFeasibility C attr :=
  Set.inter_subset_inter_left _ (hyperFeasibility_antitone h)

/-- **Bottom witness for the entity layer.**  Fix a determinate corpus.
If the positive closure `posSetoid docs` --- the least merge forced by the
evidence --- separates every forbidden pair and unifies attributes on
every cluster it creates, then the entity feasibility set of the
corresponding corpus of single-reading hyperclaims is nonempty, witnessed
by that closure itself.  Since `posSetoid docs` is the *finest* feasible
state, `mergeCompatible_of_le` says this is the weakest attribute
hypothesis one could ask for. -/
theorem entityFeasibility_nonempty_of_posSetoid (docs : Set (Document F))
    (attr : F → Set W)
    (hneg : ∀ d ∈ docs, ∀ e ∈ d.negative_edges, ¬ posSetoid docs e.1 e.2)
    (hmc : mergeCompatible attr (posSetoid docs)) :
    (entityFeasibility (ofDocument '' docs) attr).Nonempty := by
  refine ⟨posSetoid docs, ?_, hmc⟩
  rw [hyperFeasibility_image_ofDocument]
  exact mem_multidocFeasibility_iff.mpr ⟨le_refl _, hneg⟩

/-! ## Stabilization over a finite frame universe -/

/-- Over a finite frame universe there are finitely many coreference
states: a setoid is determined by its underlying relation. -/
instance instFiniteSetoid [Finite F] : Finite (Setoid F) :=
  Finite.of_injective (fun R : Setoid F => (R.r : F → F → Prop))
    fun _ _ h => Setoid.ext fun a b => iff_of_eq (congrFun (congrFun h a) b)

/-- **Stabilization.**  Over a finite frame universe, a monotone stream of
hyperclaim corpora has eventually constant feasibility: after finitely
many claims, further claims of the stream add nothing.  The hyper lift of
`STE.antitone_eventually_eq_iInter`. -/
theorem hyperFeasibility_eventually_const [Finite F] {C : ℕ → Set (HyperClaim F)}
    (hC : Monotone C) :
    ∀ᶠ n in Filter.atTop,
      hyperFeasibility (C n) = ⋂ i, hyperFeasibility (C i) :=
  STE.antitone_eventually_eq_iInter fun _ _ h => hyperFeasibility_antitone (hC h)

/-- The same, at the entity layer. -/
theorem entityFeasibility_eventually_const [Finite F] {C : ℕ → Set (HyperClaim F)}
    (attr : F → Set W) (hC : Monotone C) :
    ∀ᶠ n in Filter.atTop,
      entityFeasibility (C n) attr = ⋂ i, entityFeasibility (C i) attr :=
  STE.antitone_eventually_eq_iInter fun _ _ h => entityFeasibility_antitone attr (hC h)

end STE.HyperCoref
