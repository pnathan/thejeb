/-
Set Theoretic Estimation applied to Multidocument Frame Coreference.

We formalize multidocument frame coreference resolution algebraically, 
treating extraction as a given. The solution space is the set of all 
valid equivalence relations (partitions) over the universe of frames.
-/
import Mathlib.Data.Setoid.Basic
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
  { R : Setoid F | (∀ e ∈ doc.positive_edges, R.Rel e.1 e.2) ∧
                   (∀ e ∈ doc.negative_edges, ¬ R.Rel e.1 e.2) }

/-- The multidocument feasibility set is the intersection of the property
sets of a collection of documents. This operation is trivially commutative. -/
def multidocFeasibility (docs : Set (Document F)) : Set (Setoid F) :=
  ⋂ d ∈ docs, propertySet d

/-- Adding a document shrinks the feasibility set (Information Monotonicity).
This aligns with `partialFeasibilitySet_antitone` from Combettes. -/
theorem feasibility_antitone {D D' : Set (Document F)} (h : D ⊆ D') :
    multidocFeasibility D' ⊆ multidocFeasibility D := by
  intro R hR
  simp only [multidocFeasibility, Set.mem_iInter] at hR ⊢
  intro d hd
  exact hR d (h hd)

/-- If documents contain contradictory discourse constraints
(a cohomological obstruction in Sheaf terms), the feasibility set is empty. -/
theorem empty_feasibility_of_contradiction {d₁ d₂ : Document F}
    (docs : Set (Document F)) (hd₁ : d₁ ∈ docs) (hd₂ : d₂ ∈ docs)
    (f₁ f₂ : F)
    (h_pos : (f₁, f₂) ∈ d₁.positive_edges)
    (h_neg : (f₁, f₂) ∈ d₂.negative_edges) :
    multidocFeasibility docs = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro R hR
  have hR_d₁ := Set.mem_iInter₂.mp hR d₁ hd₁
  have hR_d₂ := Set.mem_iInter₂.mp hR d₂ hd₂
  have h_rel := hR_d₁.1 (f₁, f₂) h_pos
  have h_not_rel := hR_d₂.2 (f₁, f₂) h_neg
  exact h_not_rel h_rel

end STE.FrameCoref
