/-
Finite minimal document supports for normalization conclusions.

The theorem is intentionally semantic: it proves that every conclusion already
supported by a finite corpus has an inclusion-minimal finite subcorpus that
still supports it.  It does not claim that computing such a support is cheap.
-/
import Ste.DynamicFrame.Laws
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find

namespace STE.DynamicFrame

universe uDoc uClaim uFrame uHypothesis uConstraint

/-- Every property of finite sets that holds somewhere below `D` has an
inclusion-minimal witness below `D`. -/
theorem exists_minimal_subfinset {α : Type*} [DecidableEq α]
    (P : Finset α → Prop) (D : Finset α) (hD : P D) :
    ∃ E : Finset α,
      E ⊆ D ∧ P E ∧ ∀ F : Finset α, F ⊂ E → ¬P F := by
  classical
  let Q : Nat → Prop := fun n =>
    ∃ E : Finset α, E ⊆ D ∧ P E ∧ E.card = n
  have hQ : ∃ n, Q n :=
    ⟨D.card, D, fun _ h => h, hD, rfl⟩
  obtain ⟨E, hED, hE, hcard⟩ := Nat.find_spec hQ
  refine ⟨E, hED, hE, ?_⟩
  intro F hFE hF
  have hFD : F ⊆ D := fun _ hx => hED (hFE.1 hx)
  have hQF : Q F.card := ⟨F, hFD, hF, rfl⟩
  have hmin : Nat.find hQ ≤ F.card := Nat.find_min' hQ hQF
  have hlt : F.card < E.card := Finset.card_lt_card hFE
  rw [hcard] at hlt
  exact (Nat.not_lt_of_ge hmin) hlt

namespace Model

variable {Document : Type uDoc} {Claim : Type uClaim} {Frame : Type uFrame}
variable {Hypothesis : Type uHypothesis} {Constraint : Type uConstraint}
variable (M : Model Document Claim Frame Hypothesis Constraint)

/-- A finite document set supports a must-coreference conclusion when its
normalization problem is consistent and every feasible world merges the pair. -/
def SupportsMust (D : Finset Document) (c d : Claim) : Prop :=
  M.Consistent (D : Set Document) ∧ M.MustSame (D : Set Document) c d

/-- The analogous finite support predicate for a cannot-coreference
conclusion. -/
def SupportsCannot (D : Finset Document) (c d : Claim) : Prop :=
  M.Consistent (D : Set Document) ∧ M.CannotSame (D : Set Document) c d

/-- An inclusion-minimal finite support for must-coreference. -/
def MinimalMustSupport (D : Finset Document) (c d : Claim) : Prop :=
  M.SupportsMust D c d ∧
    ∀ E : Finset Document, E ⊂ D → ¬M.SupportsMust E c d

/-- An inclusion-minimal finite support for cannot-coreference. -/
def MinimalCannotSupport (D : Finset Document) (c d : Claim) : Prop :=
  M.SupportsCannot D c d ∧
    ∀ E : Finset Document, E ⊂ D → ¬M.SupportsCannot E c d

/-- Every finitely supported must-coreference fact has a minimal document
certificate contained in the original corpus. -/
theorem exists_minimal_mustSupport [DecidableEq Document]
    {D : Finset Document} {c d : Claim} (hD : M.SupportsMust D c d) :
    ∃ E : Finset Document,
      E ⊆ D ∧ M.MinimalMustSupport E c d := by
  obtain ⟨E, hED, hE, hmin⟩ :=
    exists_minimal_subfinset (fun F => M.SupportsMust F c d) D hD
  exact ⟨E, hED, hE, hmin⟩

/-- Every finitely supported cannot-coreference fact has a minimal document
certificate contained in the original corpus. -/
theorem exists_minimal_cannotSupport [DecidableEq Document]
    {D : Finset Document} {c d : Claim} (hD : M.SupportsCannot D c d) :
    ∃ E : Finset Document,
      E ⊆ D ∧ M.MinimalCannotSupport E c d := by
  obtain ⟨E, hED, hE, hmin⟩ :=
    exists_minimal_subfinset (fun F => M.SupportsCannot F c d) D hD
  exact ⟨E, hED, hE, hmin⟩

end Model

end STE.DynamicFrame
