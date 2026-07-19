/-
Core set theoretic estimation (STE) framework.

Reference:
  P. L. Combettes, "The Foundations of Set Theoretic Estimation,"
  Proceedings of the IEEE, vol. 81, no. 2, pp. 182-208, Feb. 1993.
  doi:10.1109/5.214546.

Combettes, Section II: an estimation problem is specified by a solution
space `Ξ`, an index set `I` of pieces of information, and for each piece
of information a *property set* `S i ⊆ Ξ` consisting of the points of
`Ξ` consistent with that piece of information.  The *feasibility set* is
`S = ⋂ i, S i`, and a *set theoretic estimate* is any point of `S`.
-/
import Mathlib.Data.Set.Lattice

namespace STE

variable {Ξ : Type*} {I : Type*}

/-- The feasibility set of a family of property sets `S : I → Set Ξ`:
the set of points consistent with every piece of information
(Combettes 1993, §II-B, Eq. (12)). -/
def feasibilitySet (S : I → Set Ξ) : Set Ξ :=
  ⋂ i, S i

/-- Membership in the feasibility set is exactly simultaneous
membership in every property set. -/
theorem mem_feasibilitySet {S : I → Set Ξ} {a : Ξ} :
    a ∈ feasibilitySet S ↔ ∀ i, a ∈ S i :=
  Set.mem_iInter

/-- Every feasible point satisfies each individual constraint:
the feasibility set refines every property set. -/
theorem feasibilitySet_subset (S : I → Set Ξ) (i : I) :
    feasibilitySet S ⊆ S i :=
  Set.iInter_subset S i

/-- The partial feasibility set: only the constraints indexed by `J` are
enforced.  This models estimation from a subcollection of the available
information. -/
def partialFeasibilitySet (S : I → Set Ξ) (J : Set I) : Set Ξ :=
  ⋂ i ∈ J, S i

/-- Enforcing all constraints refines enforcing some of them. -/
theorem feasibilitySet_subset_partial (S : I → Set Ξ) (J : Set I) :
    feasibilitySet S ⊆ partialFeasibilitySet S J := by
  intro a ha
  simp only [partialFeasibilitySet, Set.mem_iInter]
  intro i _
  exact mem_feasibilitySet.mp ha i

/-- **Information monotonicity** (Combettes 1993, §II-B): acquiring more
information can only shrink (never enlarge) the feasibility set.  Stated
as antitonicity of the partial feasibility set in the enforced index
set. -/
theorem partialFeasibilitySet_antitone (S : I → Set Ξ) {J K : Set I}
    (hJK : J ⊆ K) :
    partialFeasibilitySet S K ⊆ partialFeasibilitySet S J := by
  intro a ha
  simp only [partialFeasibilitySet, Set.mem_iInter] at ha ⊢
  exact fun i hi => ha i (hJK hi)

/-- Enforcing every constraint recovers the feasibility set. -/
theorem partialFeasibilitySet_univ (S : I → Set Ξ) :
    partialFeasibilitySet S Set.univ = feasibilitySet S := by
  simp [partialFeasibilitySet, feasibilitySet]

/-- A family of property sets is *fair* for the true estimand `h` when
each piece of information is genuinely satisfied by `h` (Combettes 1993,
§II-C: every property set contains the true object). -/
def Fair (S : I → Set Ξ) (h : Ξ) : Prop :=
  ∀ i, h ∈ S i

/-- Fairness is precisely membership of the truth in the feasibility
set. -/
theorem fair_iff_mem_feasibilitySet {S : I → Set Ξ} {h : Ξ} :
    Fair S h ↔ h ∈ feasibilitySet S :=
  mem_feasibilitySet.symm

/-- **Consistency of fair information** (Combettes 1993, §II-C): if the
information is fair for some estimand then the estimation problem is
consistent, i.e. the feasibility set is nonempty. -/
theorem feasibilitySet_nonempty_of_fair {S : I → Set Ξ} {h : Ξ}
    (hf : Fair S h) :
    (feasibilitySet S).Nonempty :=
  ⟨h, fair_iff_mem_feasibilitySet.mp hf⟩

/-- Contrapositive: an inconsistent problem (`S = ∅`) proves that at
least one piece of information is unfair for every candidate truth.
This is the set theoretic detection-of-invalid-information principle
(Combettes 1993, §II-E). -/
theorem exists_unfair_of_feasibilitySet_eq_empty {S : I → Set Ξ}
    (hS : feasibilitySet S = ∅) (h : Ξ) :
    ∃ i, h ∉ S i := by
  by_contra hcon
  push_neg at hcon
  have : h ∈ feasibilitySet S := mem_feasibilitySet.mpr hcon
  rw [hS] at this
  exact this

/-- The information is *ideal* for `h` when the feasibility set pins
down exactly the true estimand (Combettes 1993, §II-C). -/
def Ideal (S : I → Set Ξ) (h : Ξ) : Prop :=
  feasibilitySet S = {h}

/-- Ideal information is fair. -/
theorem Ideal.fair {S : I → Set Ξ} {h : Ξ} (hi : Ideal S h) : Fair S h := by
  rw [fair_iff_mem_feasibilitySet, hi]
  rfl

/-- Under ideal information, every set theoretic estimate is the truth:
feasibility alone identifies the estimand. -/
theorem Ideal.eq_of_mem {S : I → Set Ξ} {h a : Ξ} (hi : Ideal S h)
    (ha : a ∈ feasibilitySet S) : a = h := by
  rw [hi] at ha
  exact ha

/-- Idealness characterized: the information is ideal iff it is fair and
any two feasible points coincide. -/
theorem ideal_iff_fair_and_subsingleton {S : I → Set Ξ} {h : Ξ} :
    Ideal S h ↔ Fair S h ∧ ∀ a ∈ feasibilitySet S, a = h := by
  constructor
  · exact fun hi => ⟨hi.fair, fun _ ha => hi.eq_of_mem ha⟩
  · rintro ⟨hf, huniq⟩
    apply Set.eq_singleton_iff_unique_mem.mpr
    exact ⟨fair_iff_mem_feasibilitySet.mp hf, huniq⟩

end STE
