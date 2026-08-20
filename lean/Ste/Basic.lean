/-
Core set theoretic estimation (STE) framework.

Reference:
  P. L. Combettes, "The Foundations of Set Theoretic Estimation,"
  Proceedings of the IEEE, vol. 81, no. 2, pp. 182-208, Feb. 1993.
  doi:10.1109/5.214546.

Combettes, Section II-C ("Set Theoretic Formulation"): an estimation
problem is specified by a solution space `Ξ`, an index set `I` of pieces
of information, and for each piece of information a *property set*
`S i ⊆ Ξ` (Eq. (3): `Sᵢ = {a ∈ Ξ | Ψᵢ(a) ≥ ψᵢ}`) consisting of the
estimates consistent with that piece of information.  The *feasibility
set* (there called the solution set) is `S = ⋂ i, S i` (Eq. (4)), and a
*set theoretic estimate* is any point of `S`.  A formulation is
*consistent* if `S ≠ ∅`, *fair* if `h ∈ S`, and *ideal* if `S = {h}`,
where `h` is the true object (estimandum).

We mechanize the crisp case, where each `Ψᵢ` is `{0,1}`-valued so the
property set is an ordinary subset of `Ξ`; the fuzzy/graded case
(`Ψᵢ : Ξ → [0,1]`) is a natural generalization left as future work.
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic

namespace STE

variable {Ξ : Type*} {I : Type*}

/-- The feasibility set of a family of property sets `S : I → Set Ξ`:
the set of points consistent with every piece of information
(Combettes 1993, §II-C, Eq. (4)). -/
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

/-- **Information monotonicity**: acquiring more information can only
shrink (never enlarge) the feasibility set.  A direct consequence of the
intersection structure of the feasibility set (Combettes 1993, §II-C,
Eq. (4)), stated here as antitonicity of the partial feasibility set in
the enforced index set. -/
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
This is the set theoretic detection-of-invalid-information principle: an
inconsistent formulation (Combettes 1993, §II-C, Fig. 1(a)) proves some
property set is in error. -/
theorem exists_unfair_of_feasibilitySet_eq_empty {S : I → Set Ξ}
    (hS : feasibilitySet S = ∅) (h : Ξ) :
    ∃ i, h ∉ S i := by
  rw [← not_forall]
  intro hall
  have : h ∈ feasibilitySet S := mem_feasibilitySet.mpr hall
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

/-- **Stabilization of a shrinking sequence of sets over a finite space**:
an antitone sequence of subsets of a finite type is eventually equal to
its total intersection.  This is the order-theoretic content behind
"finitely many observations already suffice": in a finite solution space
information monotonicity cannot keep shrinking forever. -/
theorem antitone_eventually_eq_iInter {Ξ : Type*} [Finite Ξ] {f : ℕ → Set Ξ}
    (hf : Antitone f) : ∀ᶠ n in Filter.atTop, f n = ⋂ i, f i := by
  -- pick an index whose cardinality is minimal
  have hne : (Set.range fun n => (f n).ncard).Nonempty := ⟨_, ⟨0, rfl⟩⟩
  obtain ⟨N, hN⟩ : ∃ N, (f N).ncard = sInf (Set.range fun n => (f n).ncard) :=
    Nat.sInf_mem hne
  have hmin : ∀ m, (f N).ncard ≤ (f m).ncard := by
    intro m
    rw [hN]
    exact Nat.sInf_le ⟨m, rfl⟩
  have hstab : ∀ m, N ≤ m → f m = f N := fun m hm =>
    Set.eq_of_subset_of_ncard_le (hf hm) (hmin m) (Set.toFinite _)
  have hiInter : ⋂ i, f i = f N := by
    apply Set.Subset.antisymm (Set.iInter_subset _ N)
    refine Set.subset_iInter fun i => ?_
    rcases le_total N i with h | h
    · rw [hstab i h]
    · exact hf h
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  rw [hstab n hn, hiInter]

end STE
