/-
Set Theoretic Estimation applied to Multidocument Frame Coreference.

We formalize multidocument frame coreference resolution algebraically,
treating extraction as a given. The solution space is the set of all
valid equivalence relations (partitions) over the universe of frames.

Relationship to `Ste.Coreference`: `Ste.Coreference` computes the least
setoid forced by positive evidence (the join/closure of the asserted
links, `forcedCoref`); this file characterizes the *full feasible set*
once negative evidence — explicit non-coreference constraints — is added
to the picture. The two meet in `multidocFeasibility_nonempty_iff`: the
feasibility set is nonempty exactly when no negative edge is already
forced by the positive evidence, i.e. when no negative edge lies inside a
positive component.
-/
import Mathlib.Data.Setoid.Basic
import Mathlib.Logic.Relation
import Ste.Basic

namespace STE.FrameCoref

variable {F : Type*}

/-- A document provides local semantic information by extracting
positive coreference links and negative discourse constraints
(e.g., mutually exclusive events). -/
structure Document (F : Type*) where
  /-- Frames that are claimed to corefer. -/
  positive_edges : Set (F × F)
  /-- Frames that are explicitly claimed to NOT corefer (discourse aware). -/
  negative_edges : Set (F × F)

/-- The property set for a document is the set of all global equivalence
relations (coreference states) that perfectly respect the document's
local constraints. -/
def propertySet (doc : Document F) : Set (Setoid F) :=
  { R : Setoid F | (∀ e ∈ doc.positive_edges, R e.1 e.2) ∧
                   (∀ e ∈ doc.negative_edges, ¬ R e.1 e.2) }

/-- The multidocument feasibility set: the STE partial feasibility set of
the family `propertySet`, with the active documents as the enforced index
set. -/
def multidocFeasibility (docs : Set (Document F)) : Set (Setoid F) :=
  STE.partialFeasibilitySet propertySet docs

/-- Adding a document shrinks the feasibility set (Information Monotonicity).
This is exactly `partialFeasibilitySet_antitone` from Combettes. -/
theorem feasibility_antitone {D D' : Set (Document F)} (h : D ⊆ D') :
    multidocFeasibility D' ⊆ multidocFeasibility D :=
  STE.partialFeasibilitySet_antitone propertySet h

/-- Membership in the multidocument feasibility set, unfolded. -/
theorem mem_multidocFeasibility {docs : Set (Document F)} {R : Setoid F} :
    R ∈ multidocFeasibility docs ↔ ∀ d ∈ docs, R ∈ propertySet d := by
  simp only [multidocFeasibility, STE.partialFeasibilitySet, Set.mem_iInter]

/-- If documents contain contradictory discourse constraints — one asserts
a coreference the other forbids — the feasibility set is empty; cf. the
gluing-failure picture in `Ste.CechObstruction`. -/
theorem empty_feasibility_of_contradiction {d₁ d₂ : Document F}
    (docs : Set (Document F)) (hd₁ : d₁ ∈ docs) (hd₂ : d₂ ∈ docs)
    (f₁ f₂ : F)
    (h_pos : (f₁, f₂) ∈ d₁.positive_edges)
    (h_neg : (f₁, f₂) ∈ d₂.negative_edges) :
    multidocFeasibility docs = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro R hR
  rw [mem_multidocFeasibility] at hR
  exact (hR d₂ hd₂).2 (f₁, f₂) h_neg ((hR d₁ hd₁).1 (f₁, f₂) h_pos)

/-- An inconsistent corpus proves some document's information is unfair for
any candidate truth: the STE detection-of-invalid-information principle
(`STE.exists_unfair_of_feasibilitySet_eq_empty`) transported to the
partial (active-document) feasibility set. -/
theorem exists_unfair_of_multidocFeasibility_eq_empty
    {docs : Set (Document F)} (hdocs : multidocFeasibility docs = ∅)
    (R : Setoid F) : ∃ d, R ∉ propertySet d := by
  apply STE.exists_unfair_of_feasibilitySet_eq_empty (S := propertySet)
  rw [← STE.partialFeasibilitySet_univ]
  exact Set.eq_empty_of_subset_empty
    (hdocs ▸ STE.partialFeasibilitySet_antitone propertySet (Set.subset_univ docs))

/-! ## Degenerate documents -/

/-- A document forbidding a frame from coreferring with itself is
unsatisfiable: no equivalence relation can violate reflexivity. -/
theorem propertySet_eq_empty_of_refl_neg {doc : Document F} {f : F}
    (h : (f, f) ∈ doc.negative_edges) : propertySet (F := F) doc = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro R ⟨-, hn⟩
  exact hn (f, f) h (R.refl' f)

/-- A single document that both asserts and forbids the same coreference
is unsatisfiable. -/
theorem propertySet_eq_empty_of_mem_both {doc : Document F} {f₁ f₂ : F}
    (hp : (f₁, f₂) ∈ doc.positive_edges) (hn : (f₁, f₂) ∈ doc.negative_edges) :
    propertySet (F := F) doc = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro R ⟨hpos, hneg⟩
  exact hneg (f₁, f₂) hn (hpos (f₁, f₂) hp)

/-- Coreference evidence is symmetric: reversing every asserted and
forbidden edge does not change which coreference states are admissible,
because the candidate states are equivalence relations. -/
theorem propertySet_swap (doc : Document F) :
    propertySet (F := F) ⟨Prod.swap '' doc.positive_edges, Prod.swap '' doc.negative_edges⟩
      = propertySet doc := by
  ext R
  constructor
  · rintro ⟨hp, hn⟩
    refine ⟨fun e he => ?_, fun e he h => ?_⟩
    · exact R.symm' (hp (Prod.swap e) ⟨e, he, rfl⟩)
    · exact hn (Prod.swap e) ⟨e, he, rfl⟩ (R.symm' h)
  · rintro ⟨hp, hn⟩
    refine ⟨fun e he => ?_, fun e he h => ?_⟩
    · obtain ⟨a, ha, rfl⟩ := he
      exact R.symm' (hp a ha)
    · obtain ⟨a, ha, rfl⟩ := he
      exact hn a ha (R.symm' h)

/-- Pooling two corpora intersects their feasibility sets. -/
theorem multidocFeasibility_union (D D' : Set (Document F)) :
    multidocFeasibility (D ∪ D') = multidocFeasibility D ∩ multidocFeasibility D' := by
  simp only [multidocFeasibility, STE.partialFeasibilitySet, Set.biInter_union]

/-! ## The positive closure and the feasibility criterion -/

/-- The raw positive evidence relation of a corpus: `x` and `y` are
directly asserted to corefer by some active document. -/
def posRel (docs : Set (Document F)) : F → F → Prop :=
  fun x y => ∃ d ∈ docs, (x, y) ∈ d.positive_edges

/-- The least setoid forced by the positive evidence of a corpus: the
equivalence closure of `posRel`. This is the `Ste.Coreference`
"forced coreference" reading, specialized to frame documents. -/
def posSetoid (docs : Set (Document F)) : Setoid F :=
  Relation.EqvGen.setoid (posRel docs)

/-- The positive evidence is below any setoid it forces. -/
theorem posSetoid_le {docs : Set (Document F)} {R : Setoid F}
    (h : ∀ d ∈ docs, ∀ e ∈ d.positive_edges, R e.1 e.2) : posSetoid docs ≤ R :=
  Setoid.eqvGen_le fun _ _ hxy => by
    obtain ⟨d, hd, hxy⟩ := hxy
    exact h d hd _ hxy

/-- Feasibility, characterized: a coreference state is feasible exactly
when it dominates the positive closure and separates every forbidden
pair. -/
theorem mem_multidocFeasibility_iff {docs : Set (Document F)} {R : Setoid F} :
    R ∈ multidocFeasibility docs ↔
      posSetoid docs ≤ R ∧ ∀ d ∈ docs, ∀ e ∈ d.negative_edges, ¬ R e.1 e.2 := by
  rw [mem_multidocFeasibility]
  constructor
  · intro h
    exact ⟨posSetoid_le fun d hd => (h d hd).1, fun d hd => (h d hd).2⟩
  · rintro ⟨hle, hneg⟩
    refine fun d hd => ⟨fun e he => ?_, hneg d hd⟩
    exact Setoid.le_def.mp hle (Relation.EqvGen.rel e.1 e.2 ⟨d, hd, he⟩)

/-- **Feasibility criterion.** The corpus is consistent exactly when no
forbidden pair is already forced by the positive evidence — the
obstruction is a negative edge lying *inside* a positive component. The
witness in the consistent case is the positive closure itself. -/
theorem multidocFeasibility_nonempty_iff (docs : Set (Document F)) :
    (multidocFeasibility docs).Nonempty ↔
      ∀ d ∈ docs, ∀ e ∈ d.negative_edges, ¬ posSetoid docs e.1 e.2 := by
  constructor
  · rintro ⟨R, hR⟩ d hd e he hpos
    obtain ⟨hle, hneg⟩ := mem_multidocFeasibility_iff.mp hR
    exact hneg d hd e he (Setoid.le_def.mp hle hpos)
  · intro h
    exact ⟨posSetoid docs, mem_multidocFeasibility_iff.mpr ⟨le_refl _, h⟩⟩

/-- The positive closure is the smallest setoid containing every asserted
positive edge — the join reading and the "smallest adequate setoid"
reading coincide, mirroring `STE.Coreference.forcedCoref_eq_sInf`. -/
theorem posSetoid_eq_sInf (docs : Set (Document F)) :
    posSetoid docs =
      sInf {R : Setoid F | ∀ d ∈ docs, ∀ e ∈ d.positive_edges, R e.1 e.2} := by
  apply le_antisymm
  · exact le_sInf fun R hR => posSetoid_le hR
  · refine sInf_le fun d hd e he => ?_
    exact Relation.EqvGen.rel e.1 e.2 ⟨d, hd, he⟩

/-- More documents force more positive identifications. -/
theorem posSetoid_mono {D D' : Set (Document F)} (h : D ⊆ D') :
    posSetoid D ≤ posSetoid D' :=
  Setoid.eqvGen_mono fun _ _ hxy => by
    obtain ⟨d, hd, hxy⟩ := hxy
    exact ⟨d, h hd, hxy⟩

end STE.FrameCoref
