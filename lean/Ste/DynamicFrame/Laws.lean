/-
Structural laws for dynamic, set-valued frame normalization.

This module separates four effects that a mutable document corpus otherwise
conflates:

* active documents select provenance-supported constraints;
* feasible exact normalizations vary contravariantly with document inclusion;
* certain coreference facts grow as the feasible set shrinks;
* the quotient of active claims by certain coreference varies covariantly.

The resulting insertion/deletion asymmetry is the formal core of the dynamic
database problem.
-/
import Ste.DynamicFrame

namespace STE.DynamicFrame

universe uDoc uClaim uFrame uHypothesis uConstraint

namespace Model

variable {Document : Type uDoc} {Claim : Type uClaim} {Frame : Type uFrame}
variable {Hypothesis : Type uHypothesis} {Constraint : Type uConstraint}
variable (M : Model Document Claim Frame Hypothesis Constraint)

/-! ## Dynamic document and provenance laws -/

/-- Removing a document can only enlarge the feasible normalization set. -/
theorem feasible_subset_after_remove (D : Set Document) (d : Document) :
    M.feasible D ⊆ M.feasible (D \ {d}) :=
  M.feasible_antitone Set.diff_subset

/-- Inserting a document twice has exactly the same semantics as inserting it
once. -/
theorem feasible_insert_idempotent (D : Set Document) (d : Document) :
    M.feasible (insert d (insert d D)) = M.feasible (insert d D) := by
  rw [Set.insert_eq_self (Set.mem_insert d D)]

/-- The order of two document insertions is semantically irrelevant. -/
theorem feasible_insert_comm (D : Set Document) (d e : Document) :
    M.feasible (insert d (insert e D)) =
      M.feasible (insert e (insert d D)) := by
  rw [Set.insert_comm d e]

/-- If `d` was not active, inserting and then removing it recovers exactly the
old feasible set. -/
theorem feasible_insert_then_remove {D : Set Document} {d : Document}
    (hd : d ∉ D) :
    M.feasible (insert d D \ {d}) = M.feasible D := by
  have hset : insert d D \ {d} = D := by
    ext x
    simp [hd, eq_comm]
  rw [hset]

/-- A constraint is newly active between `D` and `E` when all of its support is
available in `E` but not in `D`. -/
def newConstraints (D E : Set Document) : Set Constraint :=
  M.activeConstraints E \ M.activeConstraints D

/-- Constraints supported by an intersection are exactly those active in both
corpora. -/
theorem activeConstraints_inter (D E : Set Document) :
    M.activeConstraints (D ∩ E) =
      M.activeConstraints D ∩ M.activeConstraints E := by
  ext k
  simp only [activeConstraints, Set.mem_setOf_eq, Set.mem_inter_iff]
  exact Set.subset_inter_iff

/-- Every constraint active on either side is active on the union.  The reverse
inclusion can fail because a genuinely cross-document constraint may require
documents from both sides. -/
theorem activeConstraints_union_subset (D E : Set Document) :
    M.activeConstraints D ∪ M.activeConstraints E ⊆
      M.activeConstraints (D ∪ E) := by
  intro k hk
  rcases hk with hk | hk
  · exact Set.Subset.trans hk Set.subset_union_left
  · exact Set.Subset.trans hk Set.subset_union_right

/-- Ontological or logical constraints with empty document support are active
in every corpus. -/
theorem active_of_support_eq_empty {D : Set Document} {k : Constraint}
    (hk : M.support k = ∅) :
    k ∈ M.activeConstraints D := by
  rw [activeConstraints, Set.mem_setOf_eq, hk]
  exact Set.empty_subset D

/-- Adding documents decomposes into the old feasible set plus exactly the
newly activated constraints. -/
theorem mem_feasible_extension {D E : Set Document} (hDE : D ⊆ E)
    {h : Hypothesis} :
    h ∈ M.feasible E ↔
      h ∈ M.feasible D ∧
        ∀ k ∈ M.newConstraints D E, M.satisfies h k := by
  constructor
  · intro hh
    refine ⟨M.feasible_antitone hDE hh, ?_⟩
    intro k hk
    exact M.mem_feasible.mp hh k hk.1
  · rintro ⟨hD, hnew⟩
    apply M.mem_feasible.mpr
    intro k hkE
    by_cases hkD : M.support k ⊆ D
    · exact M.mem_feasible.mp hD k hkD
    · exact hnew k ⟨hkE, hkD⟩

/-- If an insertion activates no new constraints, it cannot change the
feasible normalization set. -/
theorem feasible_eq_of_no_new_constraints {D E : Set Document}
    (hDE : D ⊆ E) (hnew : M.newConstraints D E = ∅) :
    M.feasible E = M.feasible D := by
  apply Set.Subset.antisymm (M.feasible_antitone hDE)
  intro h hh
  apply M.mem_feasible.mpr
  intro k hkE
  by_cases hkD : M.support k ⊆ D
  · exact M.mem_feasible.mp hh k hkD
  · have hkNew : k ∈ M.newConstraints D E := ⟨hkE, hkD⟩
    rw [hnew] at hkNew
    exact hkNew.elim

/-- Equality of the active constraint views gives equality of semantics. -/
theorem feasible_eq_of_activeConstraints_eq {D E : Set Document}
    (h : M.activeConstraints D = M.activeConstraints E) :
    M.feasible D = M.feasible E := by
  simp only [feasible, h]

/-! ## Feasible-world restriction maps -/

/-- Restriction along `D ⊆ E` forgets the additional constraints by viewing an
`E`-feasible hypothesis as a `D`-feasible hypothesis. -/
def restrictFeasible {D E : Set Document} (hDE : D ⊆ E) :
    M.feasible E → M.feasible D :=
  fun h => ⟨h.1, M.feasible_antitone hDE h.2⟩

@[simp] theorem restrictFeasible_val {D E : Set Document} (hDE : D ⊆ E)
    (h : M.feasible E) :
    (M.restrictFeasible hDE h).1 = h.1 :=
  rfl

/-- Restriction by identity is identity. -/
theorem restrictFeasible_id (D : Set Document) :
    M.restrictFeasible (Set.Subset.rfl : D ⊆ D) = id := by
  funext h
  apply Subtype.ext
  rfl

/-- Restriction composes along document inclusions. -/
theorem restrictFeasible_comp {D E F : Set Document}
    (hDE : D ⊆ E) (hEF : E ⊆ F) :
    M.restrictFeasible hDE ∘ M.restrictFeasible hEF =
      M.restrictFeasible (Set.Subset.trans hDE hEF) := by
  funext h
  apply Subtype.ext
  rfl

/-- A small-corpus hypothesis lies in the image of restriction exactly when
that same ambient hypothesis extends to the larger corpus. -/
theorem mem_range_restrictFeasible_iff {D E : Set Document}
    (hDE : D ⊆ E) (h : M.feasible D) :
    h ∈ Set.range (M.restrictFeasible hDE) ↔ h.1 ∈ M.feasible E := by
  constructor
  · rintro ⟨hE, rfl⟩
    exact hE.2
  · intro hh
    refine ⟨⟨h.1, hh⟩, ?_⟩
    apply Subtype.ext
    rfl

/-! ## Modal coreference laws -/

theorem consistent_of_superset {D E : Set Document} (hDE : D ⊆ E) :
    M.Consistent E → M.Consistent D := by
  rintro ⟨h, hh⟩
  exact ⟨h, M.feasible_antitone hDE hh⟩

theorem inconsistent_mono {D E : Set Document} (hDE : D ⊆ E) :
    ¬M.Consistent D → ¬M.Consistent E :=
  fun hn hE => hn (M.consistent_of_superset hDE hE)

theorem maySame_refl {D : Set Document} (hc : M.Consistent D) :
    Reflexive (M.MaySame D) := by
  intro c
  obtain ⟨h, hh⟩ := hc
  exact ⟨h, hh, (M.sameFrame_equivalence h).1 c⟩

theorem maySame_symm (D : Set Document) : Symmetric (M.MaySame D) := by
  rintro c d ⟨h, hh, hcd⟩
  exact ⟨h, hh, (M.sameFrame_equivalence h).2.1 hcd⟩

theorem maySeparate_symm (D : Set Document) : Symmetric (M.MaySeparate D) := by
  rintro c d ⟨h, hh, hcd⟩
  refine ⟨h, hh, ?_⟩
  intro hdc
  exact hcd ((M.sameFrame_equivalence h).2.1 hdc)

theorem cannotSame_symm (D : Set Document) : Symmetric (M.CannotSame D) := by
  intro c d hcd h hh hdc
  exact hcd h hh ((M.sameFrame_equivalence h).2.1 hdc)

theorem not_maySeparate_self (D : Set Document) (c : Claim) :
    ¬M.MaySeparate D c c := by
  rintro ⟨h, _, hne⟩
  exact hne ((M.sameFrame_equivalence h).1 c)

theorem uncertain_symm (D : Set Document) : Symmetric (M.Uncertain D) := by
  rintro c d ⟨hs, hd⟩
  exact ⟨M.maySame_symm D hs, M.maySeparate_symm D hd⟩

theorem uncertain_irrefl (D : Set Document) : Irreflexive (M.Uncertain D) := by
  intro c hc
  exact M.not_maySeparate_self D c hc.2

theorem must_not_uncertain {D : Set Document} {c d : Claim}
    (hm : M.MustSame D c d) : ¬M.Uncertain D c d := by
  rintro ⟨_, hsep⟩
  obtain ⟨h, hh, hne⟩ := hsep
  exact hne (hm h hh)

theorem cannot_not_uncertain {D : Set Document} {c d : Claim}
    (hn : M.CannotSame D c d) : ¬M.Uncertain D c d := by
  rintro ⟨hsame, _⟩
  obtain ⟨h, hh, hs⟩ := hsame
  exact hn h hh hs

/-- More evidence can resolve uncertainty but cannot create an uncertainty
that was absent from the less constrained feasible family. -/
theorem uncertain_antitone {D E : Set Document} (hDE : D ⊆ E)
    {c d : Claim} :
    M.Uncertain E c d → M.Uncertain D c d := by
  rintro ⟨hs, hd⟩
  exact ⟨M.maySame_antitone hDE hs, M.maySeparate_antitone hDE hd⟩

/-- The four corpus-aware pair statuses.  `inconsistent` is separate because
universal statements over an empty feasible set are vacuous. -/
inductive CorefStatus where
  | inconsistent
  | must
  | cannot
  | uncertain
  deriving DecidableEq, Repr

/-- Deterministic status obtained from exact feasible-world quantification. -/
noncomputable def corefStatus (D : Set Document) (c d : Claim) : CorefStatus :=
  if hc : M.Consistent D then
    if hm : M.MustSame D c d then
      .must
    else if M.MaySame D c d then
      .uncertain
    else
      .cannot
  else
    .inconsistent

theorem corefStatus_eq_inconsistent {D : Set Document} {c d : Claim}
    (h : ¬M.Consistent D) :
    M.corefStatus D c d = .inconsistent := by
  simp [corefStatus, h]

theorem corefStatus_eq_must {D : Set Document} {c d : Claim}
    (hc : M.Consistent D) (hm : M.MustSame D c d) :
    M.corefStatus D c d = .must := by
  simp [corefStatus, hc, hm]

theorem corefStatus_eq_cannot {D : Set Document} {c d : Claim}
    (hc : M.Consistent D) (hn : M.CannotSame D c d) :
    M.corefStatus D c d = .cannot := by
  have hmay : ¬M.MaySame D c d := M.cannot_iff_not_may.mp hn
  have hmust : ¬M.MustSame D c d := by
    intro hm
    exact M.must_and_cannot_implies_inconsistent hm hn hc
  simp [corefStatus, hc, hmust, hmay]

theorem corefStatus_eq_uncertain {D : Set Document} {c d : Claim}
    (hc : M.Consistent D) (hu : M.Uncertain D c d) :
    M.corefStatus D c d = .uncertain := by
  have hmust : ¬M.MustSame D c d := fun hm => M.must_not_uncertain hm hu
  simp [corefStatus, hc, hmust, hu.1]

/-! ## Canonical-frame maps -/

/-- Inclusion of active claims along document inclusion. -/
def includeActiveClaim {D E : Set Document} (hDE : D ⊆ E) :
    M.activeClaims D → M.activeClaims E :=
  fun c => ⟨c.1, hDE c.2⟩

/-- Adding documents induces a map from old canonical frames to new canonical
frames.  It may identify old classes, so it is not generally injective. -/
def canonicalMap {D E : Set Document} (hDE : D ⊆ E) :
    M.CanonicalFrame D → M.CanonicalFrame E :=
  Quotient.map (M.includeActiveClaim hDE) (by
    intro c d hcd
    exact M.mustSame_mono hDE hcd)

end Model

end STE.DynamicFrame
