/-
Corpus-indexed worlds, partial claim restriction, and exact gluing.

The feasible-world construction is contravariant in the active document set.
Active claims themselves are covariant under insertion and only partially
restrict under deletion: a claim restricts exactly when its source remains
active.  Compatible local worlds glue precisely when no genuinely
cross-document constraint is violated.  Because all views live in one ambient
hypothesis type, a global extension of fixed local worlds is unique.
-/
import Ste.DynamicFrame.Laws

namespace STE.DynamicFrame

universe uDoc uClaim uFrame uHypothesis uConstraint

namespace Model

variable {Document : Type uDoc} {Claim : Type uClaim} {Frame : Type uFrame}
variable {Hypothesis : Type uHypothesis} {Constraint : Type uConstraint}
variable (M : Model Document Claim Frame Hypothesis Constraint)

/-- The exact worlds visible at one corpus snapshot. -/
abbrev WorldView (D : Set Document) := M.feasible D

/-- Restriction of a feasible world along document inclusion. -/
abbrev restrictWorld {D E : Set Document} (hDE : D ⊆ E) :
    M.WorldView E → M.WorldView D :=
  M.restrictFeasible hDE

theorem restrictWorld_id (D : Set Document) :
    M.restrictWorld (Set.Subset.rfl : D ⊆ D) = id :=
  M.restrictFeasible_id D

theorem restrictWorld_comp {D E F : Set Document}
    (hDE : D ⊆ E) (hEF : E ⊆ F) :
    M.restrictWorld hDE ∘ M.restrictWorld hEF =
      M.restrictWorld (Set.Subset.trans hDE hEF) :=
  M.restrictFeasible_comp hDE hEF

/-- Coreference as seen inside a corpus-dependent world and claim universe. -/
def localSame (D : Set Document) (h : M.WorldView D)
    (c d : M.activeClaims D) : Prop :=
  M.sameFrame h.1 c.1 d.1

/-- World restriction and active-claim inclusion preserve the local relation
definitionally. -/
theorem localSame_restrict {D E : Set Document} (hDE : D ⊆ E)
    (h : M.WorldView E) (c d : M.activeClaims D) :
    M.localSame D (M.restrictWorld hDE h) c d ↔
      M.localSame E h (M.includeActiveClaim hDE c)
        (M.includeActiveClaim hDE d) :=
  Iff.rfl

/-- Relational (partial) restriction of active claims.  It is deliberately not
a total function from the larger active universe: claims from deleted
documents have no target. -/
def ClaimRestricts {D E : Set Document} (_hDE : D ⊆ E)
    (cE : M.activeClaims E) (cD : M.activeClaims D) : Prop :=
  cE.1 = cD.1

theorem claimRestriction_unique {D E : Set Document} {hDE : D ⊆ E}
    {cE : M.activeClaims E} {cD cD' : M.activeClaims D}
    (h : M.ClaimRestricts hDE cE cD)
    (h' : M.ClaimRestricts hDE cE cD') :
    cD = cD' := by
  apply Subtype.ext
  exact h.symm.trans h'

theorem claimRestriction_exists_iff {D E : Set Document} {hDE : D ⊆ E}
    (cE : M.activeClaims E) :
    (∃ cD : M.activeClaims D, M.ClaimRestricts hDE cE cD) ↔
      M.claimDocument cE.1 ∈ D := by
  constructor
  · rintro ⟨cD, h⟩
    rw [h]
    exact cD.2
  · intro hc
    exact ⟨⟨cE.1, hc⟩, rfl⟩

/-- Constraints that become active only on the union and that an ambient
hypothesis violates.  These are exactly the obstruction to gluing two locally
feasible views of that hypothesis. -/
def crossObstruction (D E : Set Document) (h : Hypothesis) : Set Constraint :=
  {k | M.support k ⊆ D ∪ E ∧
       ¬M.support k ⊆ D ∧
       ¬M.support k ⊆ E ∧
       ¬M.satisfies h k}

/-- Exact local-to-global feasibility classification. -/
theorem mem_feasible_union_iff {D E : Set Document} {h : Hypothesis} :
    h ∈ M.feasible (D ∪ E) ↔
      h ∈ M.feasible D ∧
      h ∈ M.feasible E ∧
      M.crossObstruction D E h = ∅ := by
  constructor
  · intro hh
    refine ⟨M.feasible_antitone Set.subset_union_left hh,
      M.feasible_antitone Set.subset_union_right hh, ?_⟩
    ext k
    constructor
    · rintro ⟨hk, _, _, hnot⟩
      exact (hnot (M.mem_feasible.mp hh k hk)).elim
    · intro hk
      exact hk.elim
  · rintro ⟨hD, hE, hobs⟩
    apply M.mem_feasible.mpr
    intro k hk
    by_cases hkD : M.support k ⊆ D
    · exact M.mem_feasible.mp hD k hkD
    by_cases hkE : M.support k ⊆ E
    · exact M.mem_feasible.mp hE k hkE
    by_contra hsat
    have : k ∈ M.crossObstruction D E h := ⟨hk, hkD, hkE, hsat⟩
    rw [hobs] at this
    exact this.elim

/-- Two local views are compatible when they expose the same immutable
ambient exact hypothesis. -/
def Compatible {D E : Set Document}
    (hD : M.WorldView D) (hE : M.WorldView E) : Prop :=
  hD.1 = hE.1

/-- Global extensions whose restrictions are the specified local worlds. -/
def GlobalExtension {D E : Set Document}
    (hD : M.WorldView D) (hE : M.WorldView E) :=
  {h : M.WorldView (D ∪ E) //
    M.restrictWorld Set.subset_union_left h = hD ∧
    M.restrictWorld Set.subset_union_right h = hE}

/-- A fixed pair of local worlds has at most one global extension.  This is the
formal uniqueness constant: the extension type has cardinality at most one. -/
instance globalExtension_subsingleton {D E : Set Document}
    (hD : M.WorldView D) (hE : M.WorldView E) :
    Subsingleton (M.GlobalExtension hD hE) where
  allEq := by
    intro x y
    apply Subtype.ext
    apply Subtype.ext
    have hx := congrArg Subtype.val x.2.1
    have hy := congrArg Subtype.val y.2.1
    exact hx.trans hy.symm

/-- Construct the unique global world after discharging the obstruction. -/
def glue {D E : Set Document} (hD : M.WorldView D) (hE : M.WorldView E)
    (hc : M.Compatible hD hE)
    (hobs : M.crossObstruction D E hD.1 = ∅) :
    M.GlobalExtension hD hE := by
  have hE' : hD.1 ∈ M.feasible E := by
    rw [hc]
    exact hE.2
  let hU : M.WorldView (D ∪ E) :=
    ⟨hD.1, M.mem_feasible_union_iff.mpr ⟨hD.2, hE', hobs⟩⟩
  refine ⟨hU, ?_, ?_⟩
  · apply Subtype.ext
    rfl
  · apply Subtype.ext
    exact hc

/-- Gluing classification: existence is equivalent to compatibility plus a
vanishing, computable-in-the-finite-case obstruction. -/
theorem globalExtension_nonempty_iff {D E : Set Document}
    (hD : M.WorldView D) (hE : M.WorldView E) :
    Nonempty (M.GlobalExtension hD hE) ↔
      M.Compatible hD hE ∧ M.crossObstruction D E hD.1 = ∅ := by
  constructor
  · rintro ⟨hU⟩
    have hleft := congrArg Subtype.val hU.2.1
    have hright := congrArg Subtype.val hU.2.2
    refine ⟨hleft.symm.trans hright, ?_⟩
    have hmem := M.mem_feasible_union_iff.mp hU.1.2
    have hobs : M.crossObstruction D E hU.1.1 = ∅ := hmem.2.2
    change hU.1.1 = hD.1 at hleft
    rw [hleft] at hobs
    exact hobs
  · rintro ⟨hc, hobs⟩
    exact ⟨M.glue hD hE hc hobs⟩

end Model

end STE.DynamicFrame
