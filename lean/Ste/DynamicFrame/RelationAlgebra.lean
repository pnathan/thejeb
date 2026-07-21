/-
A qualified typed relation algebra for frame normalization.

The relation vocabulary is fixed, but composition laws are not guessed from
names.  A concrete world model supplies exactly the laws it validates.  Every
such pointwise law then lifts through feasible-world intersection to a sound
law for necessary (`MustRel`) conclusions.  This separates a reusable proof
principle from domain axioms that must be audited for a particular ontology.
-/
import Ste.DynamicFrame.Laws

namespace STE.DynamicFrame.RelationAlgebra

universe uDoc uClaim uFrame uHypothesis uConstraint uNode

open Model

inductive NodeSort where
  | entity
  | event
  | proposition
  deriving DecidableEq, Repr

/-- The seven relation families discussed in the frame-normalization program.
Identity is indexed by its endpoint sort; all other constructors have the
signature given by `source` and `target`. -/
inductive RelationKind where
  | strictIdentity (sort : NodeSort)
  | subevent
  | supersession
  | before
  | causes
  | repeatedInstance
  | framingDivergence
  deriving DecidableEq, Repr

def RelationKind.source : RelationKind → NodeSort
  | .strictIdentity s => s
  | .subevent | .supersession | .before | .causes | .repeatedInstance => .event
  | .framingDivergence => .proposition

def RelationKind.target : RelationKind → NodeSort
  | .strictIdentity s => s
  | .subevent | .supersession | .before | .causes | .repeatedInstance => .event
  | .framingDivergence => .proposition

/-- Audited world-level semantics.  The fields are the constants of the core
algebra: three transitivity laws, causation-to-order, repeated-instance
equivalence, and symmetric irreflexive framing divergence. -/
structure TypedRelations
    {Document : Type uDoc} {Claim : Type uClaim} {Frame : Type uFrame}
    {Hypothesis : Type uHypothesis} {Constraint : Type uConstraint}
    (M : Model Document Claim Frame Hypothesis Constraint)
    (Node : Type uNode) where
  sort : Node → NodeSort
  relates : Hypothesis → RelationKind → Node → Node → Prop
  typed : ∀ h k x y, relates h k x y →
    sort x = k.source ∧ sort y = k.target
  strictIdentity_iff : ∀ h s x y,
    relates h (.strictIdentity s) x y ↔ sort x = s ∧ x = y
  subevent_trans : ∀ h x y z,
    relates h .subevent x y → relates h .subevent y z →
      relates h .subevent x z
  supersession_trans : ∀ h x y z,
    relates h .supersession x y → relates h .supersession y z →
      relates h .supersession x z
  before_trans : ∀ h x y z,
    relates h .before x y → relates h .before y z →
      relates h .before x z
  causes_before : ∀ h x y,
    relates h .causes x y → relates h .before x y
  repeated_refl : ∀ h x, sort x = .event →
    relates h .repeatedInstance x x
  repeated_symm : ∀ h x y,
    relates h .repeatedInstance x y →
      relates h .repeatedInstance y x
  repeated_trans : ∀ h x y z,
    relates h .repeatedInstance x y →
      relates h .repeatedInstance y z →
      relates h .repeatedInstance x z
  divergence_symm : ∀ h x y,
    relates h .framingDivergence x y →
      relates h .framingDivergence y x
  divergence_irrefl : ∀ h x,
    ¬relates h .framingDivergence x x

namespace TypedRelations

variable {Document : Type uDoc} {Claim : Type uClaim} {Frame : Type uFrame}
variable {Hypothesis : Type uHypothesis} {Constraint : Type uConstraint}
variable {Node : Type uNode}
variable {M : Model Document Claim Frame Hypothesis Constraint}
variable (R : TypedRelations M Node)

/-- A typed relation forced in every feasible exact world. -/
def MustRel (D : Set Document) (k : RelationKind) (x y : Node) : Prop :=
  ∀ h ∈ M.feasible D, R.relates h k x y

theorem mustRel_typed {D : Set Document} {k : RelationKind} {x y : Node}
    (hc : M.Consistent D) (hr : R.MustRel D k x y) :
    R.sort x = k.source ∧ R.sort y = k.target := by
  obtain ⟨h, hh⟩ := hc
  exact R.typed h k x y (hr h hh)

/-- Strict identity is exactly equality on the named sort.  Consistency is
necessary in the reverse-to-data direction to avoid vacuous `MustRel`. -/
theorem mustStrictIdentity_iff {D : Set Document} (hc : M.Consistent D)
    (s : NodeSort) (x y : Node) :
    R.MustRel D (.strictIdentity s) x y ↔ R.sort x = s ∧ x = y := by
  constructor
  · intro hr
    obtain ⟨h, hh⟩ := hc
    exact (R.strictIdentity_iff h s x y).mp (hr h hh)
  · rintro ⟨hs, rfl⟩ h _
    exact (R.strictIdentity_iff h s x x).mpr ⟨hs, rfl⟩

theorem mustSubevent_trans (D : Set Document) {x y z : Node}
    (hxy : R.MustRel D .subevent x y)
    (hyz : R.MustRel D .subevent y z) :
    R.MustRel D .subevent x z := by
  intro h hh
  exact R.subevent_trans h x y z (hxy h hh) (hyz h hh)

theorem mustSupersession_trans (D : Set Document) {x y z : Node}
    (hxy : R.MustRel D .supersession x y)
    (hyz : R.MustRel D .supersession y z) :
    R.MustRel D .supersession x z := by
  intro h hh
  exact R.supersession_trans h x y z (hxy h hh) (hyz h hh)

theorem mustBefore_trans (D : Set Document) {x y z : Node}
    (hxy : R.MustRel D .before x y)
    (hyz : R.MustRel D .before y z) :
    R.MustRel D .before x z := by
  intro h hh
  exact R.before_trans h x y z (hxy h hh) (hyz h hh)

theorem mustCausesBefore (D : Set Document) {x y : Node}
    (hxy : R.MustRel D .causes x y) :
    R.MustRel D .before x y := by
  intro h hh
  exact R.causes_before h x y (hxy h hh)

theorem mustRepeated_refl (D : Set Document) {x : Node}
    (hx : R.sort x = .event) :
    R.MustRel D .repeatedInstance x x := by
  intro h _
  exact R.repeated_refl h x hx

theorem mustRepeated_symm (D : Set Document) {x y : Node}
    (hxy : R.MustRel D .repeatedInstance x y) :
    R.MustRel D .repeatedInstance y x := by
  intro h hh
  exact R.repeated_symm h x y (hxy h hh)

theorem mustRepeated_trans (D : Set Document) {x y z : Node}
    (hxy : R.MustRel D .repeatedInstance x y)
    (hyz : R.MustRel D .repeatedInstance y z) :
    R.MustRel D .repeatedInstance x z := by
  intro h hh
  exact R.repeated_trans h x y z (hxy h hh) (hyz h hh)

theorem mustDivergence_symm (D : Set Document) {x y : Node}
    (hxy : R.MustRel D .framingDivergence x y) :
    R.MustRel D .framingDivergence y x := by
  intro h hh
  exact R.divergence_symm h x y (hxy h hh)

theorem not_mustDivergence_self {D : Set Document} (hc : M.Consistent D)
    (x : Node) :
    ¬R.MustRel D .framingDivergence x x := by
  rintro hr
  obtain ⟨h, hh⟩ := hc
  exact R.divergence_irrefl h x (hr h hh)

/-- One explicitly admitted binary composition rule. -/
structure CompositionRule where
  left : RelationKind
  right : RelationKind
  result : RelationKind
  sound : ∀ h x y z,
    R.relates h left x y → R.relates h right y z →
      R.relates h result x z

/-- Every audited world-level composition rule is preserved with constant
one-step proof overhead by feasible-world intersection. -/
theorem must_compose (D : Set Document) (rule : R.CompositionRule)
    {x y z : Node}
    (hxy : R.MustRel D rule.left x y)
    (hyz : R.MustRel D rule.right y z) :
    R.MustRel D rule.result x z := by
  intro h hh
  exact rule.sound h x y z (hxy h hh) (hyz h hh)

end TypedRelations

end STE.DynamicFrame.RelationAlgebra
