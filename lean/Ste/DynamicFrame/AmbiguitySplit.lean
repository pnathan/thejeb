/-
Insertion-induced splitting of ambiguity envelopes.

The authoritative semantic state is the feasible family of exact partitions.
Its existential summary `MaySame` can lose edges when a new property set is
applied.  Consequently a presentation envelope built from possible
coreference can split even though the universal `MustSame` quotient can only
coarsen under insertion.  This module states the general law, gives finite
cardinality bounds, and constructs the red-Toyota / burgundy-BMW witness that
motivated the distinction.
-/
import Ste.DynamicFrame.Laws
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.DeriveFintype

namespace STE.DynamicFrame

universe uDoc uClaim uFrame uHypothesis uConstraint

namespace Model

variable {Document : Type uDoc} {Claim : Type uClaim} {Frame : Type uFrame}
variable {Hypothesis : Type uHypothesis} {Constraint : Type uConstraint}
variable (M : Model Document Claim Frame Hypothesis Constraint)

/-- The claims that can share an exact frame with `c` in at least one
currently feasible partition.  This is an ambiguity-preserving presentation
envelope, not an equivalence class: `MaySame` need not be transitive. -/
def mayEnvelope (D : Set Document) (c : Claim) : Set Claim :=
  {d | M.MaySame D c d}

@[simp] theorem mem_mayEnvelope {D : Set Document} {c d : Claim} :
    d ∈ M.mayEnvelope D c ↔ M.MaySame D c d :=
  Iff.rfl

/-- Property-set application can only shrink a possible-coreference
envelope. -/
theorem mayEnvelope_antitone {D E : Set Document} (hDE : D ⊆ E)
    (c : Claim) :
    M.mayEnvelope E c ⊆ M.mayEnvelope D c := by
  intro d hd
  exact M.maySame_antitone hDE hd

/-- An insertion resolves the old ambiguity between `c` and `d` apart when
both merge and split were feasible before, but every surviving exact
partition now separates them. -/
def ResolvesApart (D E : Set Document) (c d : Claim) : Prop :=
  M.Uncertain D c d ∧ M.CannotSame E c d

/-- A resolved-apart pair is a constructive witness that the later envelope
is a proper subset of the earlier envelope. -/
theorem mayEnvelope_split_witness {D E : Set Document} (hDE : D ⊆ E)
    {c d : Claim} (hsplit : M.ResolvesApart D E c d) :
    M.mayEnvelope E c ⊆ M.mayEnvelope D c ∧
      d ∈ M.mayEnvelope D c ∧ d ∉ M.mayEnvelope E c := by
  refine ⟨M.mayEnvelope_antitone hDE c, hsplit.1.1, ?_⟩
  exact (M.cannot_iff_not_may.mp hsplit.2)

/-- Under consistency, resolving a pair apart also proves that it is not a
member of the later must-coreference class. -/
theorem not_mustSame_of_resolvesApart {D E : Set Document}
    {c d : Claim} (hconsistent : M.Consistent E)
    (hsplit : M.ResolvesApart D E c d) :
    ¬M.MustSame E c d := by
  intro hmust
  exact M.must_and_cannot_implies_inconsistent hmust hsplit.2 hconsistent

section Finite

variable [Fintype Claim]

/-- Exact finite representation of one possible-coreference envelope. -/
noncomputable def finiteMayEnvelope (D : Set Document) (c : Claim) :
    Finset Claim := by
  classical
  exact Finset.univ.filter (fun d => M.MaySame D c d)

@[simp] theorem mem_finiteMayEnvelope {D : Set Document} {c d : Claim} :
    d ∈ M.finiteMayEnvelope D c ↔ M.MaySame D c d := by
  classical
  simp [finiteMayEnvelope]

theorem finiteMayEnvelope_subset {D E : Set Document} (hDE : D ⊆ E)
    (c : Claim) :
    M.finiteMayEnvelope E c ⊆ M.finiteMayEnvelope D c := by
  intro d hd
  exact M.mem_finiteMayEnvelope.mpr
    (M.maySame_antitone hDE (M.mem_finiteMayEnvelope.mp hd))

/-- The explicit envelope stores at most the ambient number of claims. -/
theorem finiteMayEnvelope_card_le (D : Set Document) (c : Claim) :
    (M.finiteMayEnvelope D c).card ≤ Fintype.card Claim := by
  classical
  simpa using Finset.card_le_card (Finset.subset_univ (M.finiteMayEnvelope D c))

/-- Every concrete resolved-apart witness removes at least one member, hence
strictly decreases the finite envelope cardinality. -/
theorem finiteMayEnvelope_card_lt_of_resolvesApart
    {D E : Set Document} (hDE : D ⊆ E) {c d : Claim}
    (hsplit : M.ResolvesApart D E c d) :
    (M.finiteMayEnvelope E c).card <
      (M.finiteMayEnvelope D c).card := by
  apply Finset.card_lt_card
  refine ⟨M.finiteMayEnvelope_subset hDE c, ?_⟩
  intro hreverse
  have hdOld : d ∈ M.finiteMayEnvelope D c :=
    M.mem_finiteMayEnvelope.mpr hsplit.1.1
  have hdNew : d ∈ M.finiteMayEnvelope E c := hreverse hdOld
  exact (M.cannot_iff_not_may.mp hsplit.2)
    (M.mem_finiteMayEnvelope.mp hdNew)

/-- Number of candidates removed from one envelope by an update. -/
noncomputable def envelopeReduction
    (D E : Set Document) (c : Claim) : Nat :=
  (M.finiteMayEnvelope D c).card - (M.finiteMayEnvelope E c).card

/-- A witnessed split has positive exact reduction. -/
theorem envelopeReduction_pos_of_resolvesApart
    {D E : Set Document} (hDE : D ⊆ E) {c d : Claim}
    (hsplit : M.ResolvesApart D E c d) :
    0 < M.envelopeReduction D E c := by
  exact Nat.sub_pos_iff_lt.mpr
    (M.finiteMayEnvelope_card_lt_of_resolvesApart hDE hsplit)

/-- The unconditional per-envelope reduction bound is the ambient claim
cardinality.  The two-claim witness below attains the sharper consistent bound
of one removal from a two-member envelope. -/
theorem envelopeReduction_le_card (D E : Set Document) (c : Claim) :
    M.envelopeReduction D E c ≤ Fintype.card Claim := by
  calc
    M.envelopeReduction D E c ≤ (M.finiteMayEnvelope D c).card :=
      Nat.sub_le _ _
    _ ≤ Fintype.card Claim := M.finiteMayEnvelope_card_le D c

end Finite

end Model

/-! ## A finite red-Toyota / burgundy-BMW witness -/

namespace VehicleSplit

inductive Document where
  | colorDescriptions
  | manufacturerEvidence
  deriving DecidableEq, Fintype, Repr

inductive Claim where
  | redCar
  | burgundyCar
  deriving DecidableEq, Fintype, Repr

inductive Make where
  | toyota
  | bmw
  deriving DecidableEq, Repr

/-- The later evidence assigns incompatible manufacturer properties to the
two old descriptions. -/
def discoveredMake : Claim → Make
  | .redCar => .toyota
  | .burgundyCar => .bmw

inductive World where
  | oneVehicle
  | twoVehicles
  deriving DecidableEq, Fintype, Repr

/-- Before manufacturer evidence, the one-vehicle world assigns one make to
both descriptions; the two-vehicle world may assign different makes. -/
def interpretedMake : World → Claim → Make
  | .oneVehicle, _ => .toyota
  | .twoVehicles, .redCar => .toyota
  | .twoVehicles, .burgundyCar => .bmw

inductive Constraint where
  | distinctManufacturers
  deriving DecidableEq, Fintype, Repr

def label : World → Claim → Bool
  | .oneVehicle, _ => false
  | .twoVehicles, .redCar => false
  | .twoVehicles, .burgundyCar => true

/-- Initially both the one-vehicle and two-vehicle partitions are feasible.
The manufacturer document activates one property set, which rejects the
one-vehicle world. -/
def model : Model Document Claim Make World Constraint where
  claimDocument := fun _ => .colorDescriptions
  candidateFrames := fun _ => Set.univ
  candidateFrames_nonempty := fun _ => ⟨.toyota, Set.mem_univ _⟩
  interpretation := interpretedMake
  interpretation_mem := fun _ _ => Set.mem_univ _
  sameFrame := fun h c d => label h c = label h d
  sameFrame_equivalence := fun _ =>
    ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
  support := fun _ => {.manufacturerEvidence}
  satisfies := fun h _ => h = .twoVehicles

def initialCorpus : Set Document := {.colorDescriptions}

def enrichedCorpus : Set Document := Set.univ

theorem initial_subset_enriched : initialCorpus ⊆ enrichedCorpus :=
  Set.subset_univ _

theorem initial_feasible (h : World) : h ∈ model.feasible initialCorpus := by
  apply model.mem_feasible.mpr
  intro k hk
  cases k
  have hevidence : Document.manufacturerEvidence ∈ initialCorpus :=
    hk (by simp [model])
  simp [initialCorpus] at hevidence

theorem twoVehicles_feasible_enriched :
    World.twoVehicles ∈ model.feasible enrichedCorpus := by
  apply model.mem_feasible.mpr
  intro k _
  cases k
  rfl

theorem oneVehicle_not_feasible_enriched :
    World.oneVehicle ∉ model.feasible enrichedCorpus := by
  intro hh
  have hs := model.mem_feasible.mp hh Constraint.distinctManufacturers
    (by simp [model, enrichedCorpus])
  simp [model] at hs

theorem initial_uncertain :
    model.Uncertain initialCorpus Claim.redCar Claim.burgundyCar := by
  constructor
  · exact ⟨.oneVehicle, initial_feasible .oneVehicle, rfl⟩
  · refine ⟨.twoVehicles, initial_feasible .twoVehicles, ?_⟩
    simp [model, label]

theorem enriched_cannotSame :
    model.CannotSame enrichedCorpus Claim.redCar Claim.burgundyCar := by
  intro h hh
  cases h with
  | oneVehicle => exact (oneVehicle_not_feasible_enriched hh).elim
  | twoVehicles => simp [model, label]

theorem resolvesApart :
    model.ResolvesApart initialCorpus enrichedCorpus
      Claim.redCar Claim.burgundyCar :=
  ⟨initial_uncertain, enriched_cannotSame⟩

/-- The old `{red car, burgundy car}` possibility envelope splits: the
burgundy description is present before manufacturer evidence and absent
after it. -/
theorem toyota_bmw_envelope_split :
    model.mayEnvelope enrichedCorpus Claim.redCar ⊆
        model.mayEnvelope initialCorpus Claim.redCar ∧
      Claim.burgundyCar ∈ model.mayEnvelope initialCorpus Claim.redCar ∧
      Claim.burgundyCar ∉ model.mayEnvelope enrichedCorpus Claim.redCar :=
  model.mayEnvelope_split_witness initial_subset_enriched resolvesApart

theorem initial_red_envelope_eq_univ :
    model.finiteMayEnvelope initialCorpus Claim.redCar = Finset.univ := by
  ext d
  simp only [Model.mem_finiteMayEnvelope, Finset.mem_univ, iff_true]
  cases d
  · exact ⟨.oneVehicle, initial_feasible .oneVehicle, rfl⟩
  · exact initial_uncertain.1

theorem enriched_red_envelope_eq_singleton :
    model.finiteMayEnvelope enrichedCorpus Claim.redCar = {.redCar} := by
  ext d
  cases d with
  | redCar =>
      simp only [Model.mem_finiteMayEnvelope, Finset.mem_singleton]
      constructor
      · intro _
        trivial
      · intro _
        exact ⟨.twoVehicles, twoVehicles_feasible_enriched, rfl⟩
  | burgundyCar =>
      simp only [Model.mem_finiteMayEnvelope, Finset.mem_singleton]
      constructor
      · intro hmay
        exact (model.cannot_iff_not_may.mp enriched_cannotSame hmay).elim
      · intro hfalse
        cases hfalse

theorem enriched_burgundy_envelope_eq_singleton :
    model.finiteMayEnvelope enrichedCorpus Claim.burgundyCar = {.burgundyCar} := by
  ext d
  cases d with
  | redCar =>
      simp only [Model.mem_finiteMayEnvelope, Finset.mem_singleton]
      constructor
      · intro hmay
        exact (model.cannot_iff_not_may.mp
          (model.cannotSame_symm enrichedCorpus enriched_cannotSame) hmay).elim
      · intro hfalse
        cases hfalse
  | burgundyCar =>
      simp only [Model.mem_finiteMayEnvelope, Finset.mem_singleton]
      constructor
      · intro _
        trivial
      · intro _
        exact ⟨.twoVehicles, twoVehicles_feasible_enriched, rfl⟩

/-- The old two-claim envelope is replaced by two distinct singleton
envelopes.  This is the concrete sense in which insertion splits a presented
frame even though it only removes exact worlds. -/
theorem toyota_bmw_split_into_two_singletons :
    model.finiteMayEnvelope initialCorpus Claim.redCar = Finset.univ ∧
      model.finiteMayEnvelope enrichedCorpus Claim.redCar = {.redCar} ∧
      model.finiteMayEnvelope enrichedCorpus Claim.burgundyCar = {.burgundyCar} :=
  ⟨initial_red_envelope_eq_univ, enriched_red_envelope_eq_singleton,
    enriched_burgundy_envelope_eq_singleton⟩

/-- Exact constant for the example: one candidate is removed from a
two-claim ambiguity envelope. -/
theorem toyota_bmw_reduction_eq_one :
    model.envelopeReduction initialCorpus enrichedCorpus Claim.redCar = 1 := by
  rw [Model.envelopeReduction, initial_red_envelope_eq_univ,
    enriched_red_envelope_eq_singleton]
  decide

end VehicleSplit

end STE.DynamicFrame
