/-
Dynamic, set-valued frame normalization.

The active document set selects provenance-indexed constraints.  Exact
normalization hypotheses remain ordinary partitions (equivalence relations),
while `MustSame`, `MaySame`, and `MaySeparate` summarize the whole feasible
set without forcing an ambiguous point estimate.
-/
import Ste.Basic

namespace STE.DynamicFrame

universe uDoc uClaim uFrame uHypothesis uConstraint

/-- A fixed ambient universe for dynamic frame normalization.

Claims and constraints are immutable.  Changing `D : Set Document` merely
changes which claims are visible and which provenance-supported constraints
are enforced.  A hypothesis chooses an admissible frame interpretation and an
exact strict-coreference equivalence relation. -/
structure Model
    (Document : Type uDoc) (Claim : Type uClaim) (Frame : Type uFrame)
    (Hypothesis : Type uHypothesis) (Constraint : Type uConstraint) where
  claimDocument : Claim → Document
  candidateFrames : Claim → Set Frame
  candidateFrames_nonempty : ∀ c, (candidateFrames c).Nonempty
  interpretation : Hypothesis → Claim → Frame
  interpretation_mem : ∀ h c, interpretation h c ∈ candidateFrames c
  sameFrame : Hypothesis → Claim → Claim → Prop
  sameFrame_equivalence : ∀ h, Equivalence (sameFrame h)
  support : Constraint → Set Document
  satisfies : Hypothesis → Constraint → Prop

namespace Model

variable {Document : Type uDoc} {Claim : Type uClaim} {Frame : Type uFrame}
variable {Hypothesis : Type uHypothesis} {Constraint : Type uConstraint}
variable (M : Model Document Claim Frame Hypothesis Constraint)

/-- Claims whose immutable source document is currently active. -/
def activeClaims (D : Set Document) : Set Claim :=
  {c | M.claimDocument c ∈ D}

/-- A constraint is active exactly when all documents in its provenance
support are active.  This includes cross-document constraints. -/
def activeConstraints (D : Set Document) : Set Constraint :=
  {k | M.support k ⊆ D}

/-- The STE property set denoted by one normalization constraint. -/
def propertySet (k : Constraint) : Set Hypothesis :=
  {h | M.satisfies h k}

/-- All exact normalization hypotheses licensed by the active corpus. -/
def feasible (D : Set Document) : Set Hypothesis :=
  partialFeasibilitySet M.propertySet (M.activeConstraints D)

theorem mem_activeClaims {D : Set Document} {c : Claim} :
    c ∈ M.activeClaims D ↔ M.claimDocument c ∈ D :=
  Iff.rfl

theorem activeClaims_mono {D E : Set Document} (hDE : D ⊆ E) :
    M.activeClaims D ⊆ M.activeClaims E := by
  intro c hc
  exact hDE hc

theorem activeConstraints_mono {D E : Set Document} (hDE : D ⊆ E) :
    M.activeConstraints D ⊆ M.activeConstraints E := by
  intro k hk
  exact Set.Subset.trans hk hDE

theorem mem_feasible {D : Set Document} {h : Hypothesis} :
    h ∈ M.feasible D ↔
      ∀ k, M.support k ⊆ D → M.satisfies h k := by
  simp [feasible, activeConstraints, propertySet, partialFeasibilitySet]

/-- Adding documents activates constraints and can only remove normalization
hypotheses.  Read in reverse, document removal can restore hypotheses. -/
theorem feasible_antitone {D E : Set Document} (hDE : D ⊆ E) :
    M.feasible E ⊆ M.feasible D :=
  partialFeasibilitySet_antitone M.propertySet
    (M.activeConstraints_mono hDE)

/-- The active corpus is consistent when at least one exact normalization
hypothesis survives. -/
def Consistent (D : Set Document) : Prop :=
  (M.feasible D).Nonempty

/-- `c` and `d` corefer in every feasible exact normalization. -/
def MustSame (D : Set Document) (c d : Claim) : Prop :=
  ∀ h ∈ M.feasible D, M.sameFrame h c d

/-- At least one feasible normalization makes `c` and `d` corefer. -/
def MaySame (D : Set Document) (c d : Claim) : Prop :=
  ∃ h ∈ M.feasible D, M.sameFrame h c d

/-- At least one feasible normalization keeps `c` and `d` separate. -/
def MaySeparate (D : Set Document) (c d : Claim) : Prop :=
  ∃ h ∈ M.feasible D, ¬M.sameFrame h c d

/-- Every feasible normalization keeps `c` and `d` separate. -/
def CannotSame (D : Set Document) (c d : Claim) : Prop :=
  ∀ h ∈ M.feasible D, ¬M.sameFrame h c d

/-- The deterministic `U` marker: both merge and split remain feasible. -/
def Uncertain (D : Set Document) (c d : Claim) : Prop :=
  M.MaySame D c d ∧ M.MaySeparate D c d

theorem mustSame_refl (D : Set Document) : Reflexive (M.MustSame D) := by
  intro c h _
  exact (M.sameFrame_equivalence h).refl c

theorem mustSame_symm (D : Set Document) : Symmetric (M.MustSame D) := by
  intro c d hcd h hh
  exact (M.sameFrame_equivalence h).symm (hcd h hh)

theorem mustSame_trans (D : Set Document) : Transitive (M.MustSame D) := by
  intro c d e hcd hde h hh
  exact (M.sameFrame_equivalence h).trans (hcd h hh) (hde h hh)

/-- The intersection of all surviving exact partitions is itself an
equivalence relation.  It therefore defines the safe deterministic quotient. -/
theorem mustSame_equivalence (D : Set Document) :
    Equivalence (M.MustSame D) :=
  ⟨fun c => M.mustSame_refl D c,
    fun h => M.mustSame_symm D h,
    fun hcd hde => M.mustSame_trans D hcd hde⟩

/-- The canonical frame quotient containing only identifications forced by
every feasible hypothesis.  Uncertain links remain outside this quotient. -/
def mustSetoid (D : Set Document) : Setoid Claim where
  r := M.MustSame D
  iseqv := M.mustSame_equivalence D

/-- Restrict the safe quotient to claims whose source documents are active. -/
def activeMustSetoid (D : Set Document) : Setoid (M.activeClaims D) where
  r := fun c d => M.MustSame D c.1 d.1
  iseqv := by
    constructor
    · intro c
      exact M.mustSame_refl D c.1
    · intro c d hcd
      exact M.mustSame_symm D hcd
    · intro c d e hcd hde
      exact M.mustSame_trans D hcd hde

/-- A canonical frame is a must-coreference class of active claims. -/
abbrev CanonicalFrame (D : Set Document) :=
  Quotient (M.activeMustSetoid D)

/-- The claims forced into the same canonical frame as `c`. -/
def mustCluster (D : Set Document) (c : Claim) : Set Claim :=
  {d | M.MustSame D c d}

theorem must_implies_may {D : Set Document} {c d : Claim}
    (hc : M.Consistent D) (hm : M.MustSame D c d) :
    M.MaySame D c d := by
  obtain ⟨h, hh⟩ := hc
  exact ⟨h, hh, hm h hh⟩

theorem cannot_iff_not_may {D : Set Document} {c d : Claim} :
    M.CannotSame D c d ↔ ¬M.MaySame D c d := by
  constructor
  · intro hn ⟨h, hh, hs⟩
    exact hn h hh hs
  · intro hn h hh hs
    exact hn ⟨h, hh, hs⟩

theorem must_and_cannot_implies_inconsistent {D : Set Document} {c d : Claim}
    (hm : M.MustSame D c d) (hn : M.CannotSame D c d) :
    ¬M.Consistent D := by
  rintro ⟨h, hh⟩
  exact hn h hh (hm h hh)

/-- For a consistent corpus, a pair is forced together, forced apart, or
explicitly uncertain.  The consistency premise prevents vacuous universal
claims when no normalization survives. -/
theorem coreference_exhaustive {D : Set Document} {c d : Claim}
    (_hc : M.Consistent D) :
    M.MustSame D c d ∨ M.CannotSame D c d ∨ M.Uncertain D c d := by
  classical
  by_cases hm : M.MustSame D c d
  · exact Or.inl hm
  by_cases hy : M.MaySame D c d
  · right
    right
    refine ⟨hy, ?_⟩
    by_contra hn
    apply hm
    intro h hh
    by_contra hs
    exact hn ⟨h, hh, hs⟩
  · right
    left
    exact M.cannot_iff_not_may.mpr hy

/-- Once a must-link is established, adding constraints preserves it (unless
the enlarged corpus becomes inconsistent, which is tracked separately). -/
theorem mustSame_mono {D E : Set Document} (hDE : D ⊆ E)
    {c d : Claim} (hm : M.MustSame D c d) :
    M.MustSame E c d := by
  intro h hh
  exact hm h (M.feasible_antitone hDE hh)

/-- Once a cannot-link is established, adding constraints preserves it. -/
theorem cannotSame_mono {D E : Set Document} (hDE : D ⊆ E)
    {c d : Claim} (hn : M.CannotSame D c d) :
    M.CannotSame E c d := by
  intro h hh
  exact hn h (M.feasible_antitone hDE hh)

/-- A merge that remains possible after adding documents was already possible
before they were added. -/
theorem maySame_antitone {D E : Set Document} (hDE : D ⊆ E)
    {c d : Claim} (hy : M.MaySame E c d) :
    M.MaySame D c d := by
  obtain ⟨h, hh, hs⟩ := hy
  exact ⟨h, M.feasible_antitone hDE hh, hs⟩

/-- Likewise, a split possible in the larger corpus was possible in the
smaller one. -/
theorem maySeparate_antitone {D E : Set Document} (hDE : D ⊆ E)
    {c d : Claim} (hy : M.MaySeparate E c d) :
    M.MaySeparate D c d := by
  obtain ⟨h, hh, hs⟩ := hy
  exact ⟨h, M.feasible_antitone hDE hh, hs⟩

/-- An exact hypothesis yields the ordinary equivalence class of a claim. -/
def exactCluster (h : Hypothesis) (c : Claim) : Set Claim :=
  {d | M.sameFrame h c d}

theorem mem_exactCluster_self (h : Hypothesis) (c : Claim) :
    c ∈ M.exactCluster h c :=
  (M.sameFrame_equivalence h).refl c

end Model

end STE.DynamicFrame
