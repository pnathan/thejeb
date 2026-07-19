/-
Constraint grammar as set theoretic estimation.

This module deliberately abstracts away from any particular natural-language
parser.  It records the algebraic question: is a hard constraint-grammar
presentation over candidate parses the same structure as an STE presentation by
property sets?  For the purely eliminative/hard-constraint fragment the answer
is yes: a rule is exactly a property set of accepted parses, parsing is exactly
feasibility, and rule accumulation is exactly antitone partial feasibility.

Operations that genuinely change the candidate universe (rather than merely
filtering a fixed enriched universe of complete analyses) are not modeled by
this equivalence; they require staged maps between universes.  The theorem below
therefore verifies the precise isomorphism for the common algebraic core.
-/
import Ste.Algebra

namespace STE.ConstraintGrammar

variable {Parse Rule : Type*}

/-- A hard constraint-grammar presentation: a universe of candidate parses and a
family of rules, each interpreted as the set of parses that survive that rule. -/
structure Grammar (Parse Rule : Type*) where
  accepts : Rule → Set Parse

/-- The parses surviving every rule of a constraint grammar. -/
def parses (G : Grammar Parse Rule) : Set Parse :=
  STE.feasibilitySet G.accepts

@[simp] theorem mem_parses {G : Grammar Parse Rule} {p : Parse} :
    p ∈ parses G ↔ ∀ r, p ∈ G.accepts r :=
  STE.mem_feasibilitySet

/-- The STE presentation underlying a constraint grammar is its family of
rule-property sets. -/
def toSTE (G : Grammar Parse Rule) : Rule → Set Parse :=
  G.accepts

/-- Every STE family of property sets can be read as a hard constraint grammar. -/
def ofSTE (S : Rule → Set Parse) : Grammar Parse Rule :=
  ⟨S⟩

@[simp] theorem toSTE_ofSTE (S : Rule → Set Parse) :
    toSTE (ofSTE S : Grammar Parse Rule) = S :=
  rfl

@[simp] theorem ofSTE_toSTE (G : Grammar Parse Rule) :
    ofSTE (toSTE G) = G := by
  cases G
  rfl

/-- Hard constraint grammars and STE property-set families are isomorphic data.
This is the formal content of the CG ↔ STE algebraic identification. -/
def grammarEquivSTE : Grammar Parse Rule ≃ (Rule → Set Parse) where
  toFun := toSTE
  invFun := ofSTE
  left_inv := ofSTE_toSTE
  right_inv := toSTE_ofSTE

@[simp] theorem grammarEquivSTE_apply (G : Grammar Parse Rule) :
    grammarEquivSTE G = G.accepts :=
  rfl

@[simp] theorem parses_eq_feasibilitySet (G : Grammar Parse Rule) :
    parses G = STE.feasibilitySet (grammarEquivSTE G) :=
  rfl

/-- A fixed hard constraint grammar is a one-instance abstract STE algebra. -/
def toAlgebra (G : Grammar Parse Rule) : STE.Algebra Unit Parse Rule :=
  ⟨fun _ => G.accepts⟩

@[simp] theorem parses_eq_algebra_feasibleSet (G : Grammar Parse Rule) :
    parses G = (toAlgebra G).feasibleSet () :=
  rfl

/-- A grammar is fair for the intended parse when every rule accepts it. -/
def Fair (G : Grammar Parse Rule) (p : Parse) : Prop :=
  STE.Fair G.accepts p

/-- A grammar is ideal for the intended parse when exactly that parse survives. -/
def Ideal (G : Grammar Parse Rule) (p : Parse) : Prop :=
  STE.Ideal G.accepts p

/-- Fair hard rules preserve at least the intended parse. -/
theorem parses_nonempty_of_fair {G : Grammar Parse Rule} {p : Parse}
    (h : Fair G p) : (parses G).Nonempty :=
  STE.feasibilitySet_nonempty_of_fair h

/-- Ideal hard rules identify the intended parse. -/
theorem Ideal.eq_of_mem {G : Grammar Parse Rule} {p q : Parse}
    (h : Ideal G p) (hq : q ∈ parses G) : q = p :=
  STE.Ideal.eq_of_mem h hq

/-- Partial parsing from a subset of rules is exactly partial STE feasibility. -/
def partialParses (G : Grammar Parse Rule) (R : Set Rule) : Set Parse :=
  STE.partialFeasibilitySet G.accepts R

@[simp] theorem mem_partialParses {G : Grammar Parse Rule} {R : Set Rule}
    {p : Parse} : p ∈ partialParses G R ↔ ∀ r ∈ R, p ∈ G.accepts r := by
  simp [partialParses, STE.partialFeasibilitySet]

/-- Adding hard rules can only remove candidate parses. -/
theorem partialParses_antitone (G : Grammar Parse Rule) {R T : Set Rule}
    (hRT : R ⊆ T) : partialParses G T ⊆ partialParses G R :=
  STE.partialFeasibilitySet_antitone G.accepts hRT

/-- Keeping only a restricted rule set is grammar restriction. -/
def restrict (G : Grammar Parse Rule) (R : Set Rule) : Grammar Parse R :=
  ⟨fun r => G.accepts r⟩

@[simp] theorem parses_restrict (G : Grammar Parse Rule) (R : Set Rule) :
    parses (G.restrict R) = partialParses G R := by
  ext p
  simp [parses, restrict, partialParses, STE.feasibilitySet,
    STE.partialFeasibilitySet]

end STE.ConstraintGrammar
