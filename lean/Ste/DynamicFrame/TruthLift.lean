/-
Lifting downstream truth estimation over feasible normalization worlds.

The normalization-first architecture does not select one normalization.  It
forms a dependent feasible family of truth worlds over every surviving exact
normalization.  Universal and existential queries over this joint set recover
certain and possible downstream conclusions.
-/
import Ste.DynamicFrame.Laws

namespace STE.DynamicFrame.TruthLift

universe uDoc uClaim uFrame uHypothesis uConstraint uTruth

open Model

variable {Document : Type uDoc} {Claim : Type uClaim} {Frame : Type uFrame}
variable {Hypothesis : Type uHypothesis} {Constraint : Type uConstraint}
variable {Truth : Type uTruth}

variable (M : Model Document Claim Frame Hypothesis Constraint)

/-- The joint feasible set of a normalization hypothesis and a downstream
truth world licensed under that hypothesis. -/
def jointFeasible (T : Hypothesis → Set Truth) (D : Set Document) :
    Set (Hypothesis × Truth) :=
  {p | p.1 ∈ M.feasible D ∧ p.2 ∈ T p.1}

@[simp] theorem mem_jointFeasible {T : Hypothesis → Set Truth}
    {D : Set Document} {h : Hypothesis} {t : Truth} :
    (h, t) ∈ jointFeasible M T D ↔ h ∈ M.feasible D ∧ t ∈ T h :=
  Iff.rfl

/-- A downstream property is certain when it holds in every truth world over
every feasible normalization. -/
def Certain (T : Hypothesis → Set Truth) (D : Set Document)
    (P : Hypothesis → Truth → Prop) : Prop :=
  ∀ h ∈ M.feasible D, ∀ t ∈ T h, P h t

/-- A downstream property is possible when some jointly feasible
normalization/truth pair satisfies it. -/
def Possible (T : Hypothesis → Set Truth) (D : Set Document)
    (P : Hypothesis → Truth → Prop) : Prop :=
  ∃ h ∈ M.feasible D, ∃ t ∈ T h, P h t

theorem certain_iff_joint {T : Hypothesis → Set Truth} {D : Set Document}
    {P : Hypothesis → Truth → Prop} :
    Certain M T D P ↔ ∀ p ∈ jointFeasible M T D, P p.1 p.2 := by
  constructor
  · intro h p hp
    exact h p.1 hp.1 p.2 hp.2
  · intro h x hx t ht
    exact h (x, t) ⟨hx, ht⟩

theorem possible_iff_joint {T : Hypothesis → Set Truth} {D : Set Document}
    {P : Hypothesis → Truth → Prop} :
    Possible M T D P ↔ ∃ p ∈ jointFeasible M T D, P p.1 p.2 := by
  constructor
  · rintro ⟨h, hh, t, ht, hp⟩
    exact ⟨(h, t), ⟨hh, ht⟩, hp⟩
  · rintro ⟨⟨h, t⟩, ⟨hh, ht⟩, hp⟩
    exact ⟨h, hh, t, ht, hp⟩

/-- Certain downstream conclusions persist under document addition. -/
theorem certain_mono {T : Hypothesis → Set Truth} {D E : Set Document}
    (hDE : D ⊆ E) {P : Hypothesis → Truth → Prop}
    (hP : Certain M T D P) : Certain M T E P := by
  intro h hh t ht
  exact hP h (M.feasible_antitone hDE hh) t ht

/-- A downstream possibility surviving document addition was already possible
before the insertion. -/
theorem possible_antitone {T : Hypothesis → Set Truth} {D E : Set Document}
    (hDE : D ⊆ E) {P : Hypothesis → Truth → Prop}
    (hP : Possible M T E P) : Possible M T D P := by
  obtain ⟨h, hh, t, ht, hp⟩ := hP
  exact ⟨h, M.feasible_antitone hDE hh, t, ht, hp⟩

/-- Normalizations that support at least one downstream truth world. -/
def normalizationProjection (T : Hypothesis → Set Truth) (D : Set Document) :
    Set Hypothesis :=
  {h | ∃ t, (h, t) ∈ jointFeasible M T D}

theorem normalizationProjection_subset (T : Hypothesis → Set Truth)
    (D : Set Document) :
    normalizationProjection M T D ⊆ M.feasible D := by
  rintro h ⟨t, ht⟩
  exact ht.1

/-- If every feasible normalization admits a truth world, projecting the joint
system recovers the normalization feasible set exactly. -/
theorem normalizationProjection_eq {T : Hypothesis → Set Truth}
    {D : Set Document}
    (hne : ∀ h ∈ M.feasible D, (T h).Nonempty) :
    normalizationProjection M T D = M.feasible D := by
  apply Set.Subset.antisymm (normalizationProjection_subset M T D)
  intro h hh
  obtain ⟨t, ht⟩ := hne h hh
  exact ⟨t, hh, ht⟩

/-- Ordinary certainty in a normalization-independent truth set. -/
def CertainTruth (T : Set Truth) (P : Truth → Prop) : Prop :=
  ∀ t ∈ T, P t

/-- Ordinary possibility in a normalization-independent truth set. -/
def PossibleTruth (T : Set Truth) (P : Truth → Prop) : Prop :=
  ∃ t ∈ T, P t

/-- Commutation theorem for normalization-independent truth semantics: when
the normalization layer is consistent, universal truth after lifting is
exactly ordinary universal truth. -/
theorem certain_constant_iff {D : Set Document} (hc : M.Consistent D)
    (T : Set Truth) (P : Truth → Prop) :
    Certain M (fun _ => T) D (fun _ t => P t) ↔ CertainTruth T P := by
  constructor
  · intro hP t ht
    obtain ⟨h, hh⟩ := hc
    exact hP h hh t ht
  · intro hP h _ t ht
    exact hP t ht

/-- The existential companion: a constant truth property is jointly possible
exactly when normalization is consistent and the property is ordinarily
possible. -/
theorem possible_constant_iff {D : Set Document} (T : Set Truth)
    (P : Truth → Prop) :
    Possible M (fun _ => T) D (fun _ t => P t) ↔
      M.Consistent D ∧ PossibleTruth T P := by
  constructor
  · rintro ⟨h, hh, t, ht, hp⟩
    exact ⟨⟨h, hh⟩, ⟨t, ht, hp⟩⟩
  · rintro ⟨⟨h, hh⟩, ⟨t, ht, hp⟩⟩
    exact ⟨h, hh, t, ht, hp⟩

end STE.DynamicFrame.TruthLift
