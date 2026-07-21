/-
Stable snapshot identity and non-functional lineage for canonical frames.

A canonical frame is identified extensionally by the immutable claim
occurrences in its must-coreference class.  This set is a complete identifier
inside one snapshot and grows monotonically along the canonical map induced by
document insertion.  Across arbitrary snapshots, overlap gives a symmetric
lineage relation that supports merges, splits, and re-merges without pretending
that deletion induces a function on quotient classes.
-/
import Ste.DynamicFrame.Laws

namespace STE.DynamicFrame

universe uDoc uClaim uFrame uHypothesis uConstraint

/-- Nonempty set overlap, the abstract shape of lineage. -/
def Overlap {A : Type*} (X Y : Set A) : Prop :=
  (X ∩ Y).Nonempty

theorem overlap_refl {A : Type*} {X : Set A} (hne : X.Nonempty) :
    Overlap X X := by
  obtain ⟨x, hx⟩ := hne
  exact ⟨x, hx, hx⟩

theorem overlap_symm {A : Type*} {X Y : Set A} (h : Overlap X Y) :
    Overlap Y X := by
  obtain ⟨x, hx, hy⟩ := h
  exact ⟨x, hy, hx⟩

/-- Overlap cannot be replaced by an equivalence relation: it is not
transitive even on two immutable occurrence identifiers. -/
theorem overlap_not_transitive :
    ¬Transitive (Overlap : Set Bool → Set Bool → Prop) := by
  intro ht
  have hleft : Overlap ({false} : Set Bool) Set.univ := by
    exact ⟨false, by simp, by simp⟩
  have hright : Overlap (Set.univ : Set Bool) {true} := by
    exact ⟨true, by simp, by simp⟩
  have hbad := ht hleft hright
  simpa [Overlap] using hbad

namespace Model

variable {Document : Type uDoc} {Claim : Type uClaim} {Frame : Type uFrame}
variable {Hypothesis : Type uHypothesis} {Constraint : Type uConstraint}
variable (M : Model Document Claim Frame Hypothesis Constraint)

/-- Immutable occurrence members of one representative's active must-class. -/
def classMembers (D : Set Document) (c : M.activeClaims D) : Set Claim :=
  {x | x ∈ M.activeClaims D ∧ M.MustSame D c.1 x}

theorem classMembers_eq {D : Set Document} {c d : M.activeClaims D}
    (hcd : M.MustSame D c.1 d.1) :
    M.classMembers D c = M.classMembers D d := by
  ext x
  constructor
  · rintro ⟨hx, hcx⟩
    exact ⟨hx, M.mustSame_trans D (M.mustSame_symm D hcd) hcx⟩
  · rintro ⟨hx, hdx⟩
    exact ⟨hx, M.mustSame_trans D hcd hdx⟩

/-- A complete presentation identifier for a canonical frame at one snapshot. -/
def canonicalMembers (D : Set Document) : M.CanonicalFrame D → Set Claim :=
  Quotient.lift (M.classMembers D) (by
    intro c d hcd
    exact M.classMembers_eq hcd)

@[simp] theorem canonicalMembers_mk (D : Set Document)
    (c : M.activeClaims D) :
    M.canonicalMembers D (Quotient.mk _ c) = M.classMembers D c :=
  rfl

/-- The identifier always has at least one immutable occurrence.  This is the
lower cardinality constant for every live canonical frame. -/
theorem canonicalMembers_nonempty (D : Set Document)
    (q : M.CanonicalFrame D) :
    (M.canonicalMembers D q).Nonempty := by
  refine Quotient.inductionOn q ?_
  intro c
  exact ⟨c.1, c.2, M.mustSame_refl D c.1⟩

/-- Member sets are complete identifiers within a snapshot. -/
theorem canonicalMembers_injective (D : Set Document) :
    Function.Injective (M.canonicalMembers D) := by
  intro q r
  refine Quotient.inductionOn q ?_
  intro c
  refine Quotient.inductionOn r ?_
  intro d hsets
  change M.classMembers D c = M.classMembers D d at hsets
  apply Quotient.sound
  have hc : c.1 ∈ M.classMembers D c :=
    ⟨c.2, M.mustSame_refl D c.1⟩
  have hcd : c.1 ∈ M.classMembers D d := by
    rw [← hsets]
    exact hc
  exact M.mustSame_symm D hcd.2

/-- Stable presentation identifier: an immutable set, not an arbitrary scalar
name that would have to choose one child after a split. -/
abbrev PresentationId (Claim : Type uClaim) := Set Claim

def presentationId (D : Set Document) :
    M.CanonicalFrame D → PresentationId Claim :=
  M.canonicalMembers D

theorem presentationId_injective (D : Set Document) :
    Function.Injective (M.presentationId D) :=
  M.canonicalMembers_injective D

/-- Under document insertion, every old immutable member remains in the image
class; added evidence may merge that class with others or add new claims. -/
theorem canonicalMembers_subset_map {D E : Set Document} (hDE : D ⊆ E)
    (q : M.CanonicalFrame D) :
    M.canonicalMembers D q ⊆
      M.canonicalMembers E (M.canonicalMap hDE q) := by
  refine Quotient.inductionOn q ?_
  intro c x hx
  change x ∈ M.classMembers D c at hx
  change x ∈ M.classMembers E (M.includeActiveClaim hDE c)
  exact ⟨M.activeClaims_mono hDE hx.1, M.mustSame_mono hDE hx.2⟩

/-- Historical continuity between frames is overlap of immutable occurrence
sets.  It is intentionally relational rather than functional. -/
def Lineage {D E : Set Document}
    (q : M.CanonicalFrame D) (r : M.CanonicalFrame E) : Prop :=
  Overlap (M.canonicalMembers D q) (M.canonicalMembers E r)

theorem lineage_refl {D : Set Document} (q : M.CanonicalFrame D) :
    M.Lineage q q :=
  overlap_refl (M.canonicalMembers_nonempty D q)

theorem lineage_symm {D E : Set Document}
    {q : M.CanonicalFrame D} {r : M.CanonicalFrame E}
    (h : M.Lineage q r) : M.Lineage r q :=
  overlap_symm h

/-- Every frame has lineage to its canonical image after insertion. -/
theorem lineage_canonicalMap {D E : Set Document} (hDE : D ⊆ E)
    (q : M.CanonicalFrame D) :
    M.Lineage q (M.canonicalMap hDE q) := by
  obtain ⟨x, hx⟩ := M.canonicalMembers_nonempty D q
  exact ⟨x, hx, M.canonicalMembers_subset_map hDE q hx⟩

end Model

end STE.DynamicFrame
