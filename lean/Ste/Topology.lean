/-
Topological structure of set theoretic estimation.

References:
  P. L. Combettes, "The Foundations of Set Theoretic Estimation,"
  Proc. IEEE 81(2):182-208, 1993 — §III works in metric/Hilbert spaces
  where property sets are typically closed.

  A. H. Carlson, "Set Theoretic Estimation Applied to the Information
  Content of Ciphers and Decryption," Ph.D. dissertation, University of
  Idaho, 2012 — recasts STE over (finite/discrete) topological spaces
  rather than the metric spaces of prior implementations.

This file records the topological facts that make STE well posed:
closedness of the feasibility set, and existence of feasible points
(consistency) via compactness and the finite intersection property.
-/
import Mathlib.Topology.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Basic
import Ste.Basic

namespace STE

variable {Ξ : Type*} {I : Type*} [TopologicalSpace Ξ]

/-- If every property set is closed, the feasibility set is closed.
This is the standing hypothesis of Combettes 1993, §III (there in a
metric space; here in an arbitrary topological space, the setting of
Carlson 2012). -/
theorem isClosed_feasibilitySet {S : I → Set Ξ} (hc : ∀ i, IsClosed (S i)) :
    IsClosed (feasibilitySet S) :=
  isClosed_iInter hc

/-- The family `S` has the *finite intersection property* when every
finite subfamily of constraints is simultaneously satisfiable. -/
def FiniteConsistency (S : I → Set Ξ) : Prop :=
  ∀ u : Finset I, (⋂ i ∈ u, S i).Nonempty

/-- Fair information is finitely consistent. -/
omit [TopologicalSpace Ξ] in
theorem FiniteConsistency.of_fair {S : I → Set Ξ} {h : Ξ} (hf : Fair S h) :
    FiniteConsistency S := by
  intro u
  refine ⟨h, ?_⟩
  simp only [Set.mem_iInter]
  exact fun i _ => hf i

/-- **Existence of set theoretic estimates in a compact space**: if the
solution space is compact, every property set is closed, and every
finite subcollection of the information is consistent, then the full
estimation problem is consistent.  This is the finite-intersection-
property argument specialized to STE; it is the abstract reason STE is
well posed on the finite solution spaces of Carlson 2012 and on the
bounded closed convex constraint sets of Combettes 1993. -/
theorem feasibilitySet_nonempty_of_compact [CompactSpace Ξ]
    {S : I → Set Ξ} (hclosed : ∀ i, IsClosed (S i))
    (hfip : FiniteConsistency S) :
    (feasibilitySet S).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hcap : (Set.univ ∩ ⋂ i, S i) = ∅ := by
    rw [Set.univ_inter]
    exact hempty
  obtain ⟨u, hu⟩ :=
    isCompact_univ.elim_finite_subfamily_closed S hclosed hcap
  rw [Set.univ_inter] at hu
  have := hfip u
  rw [hu] at this
  exact Set.not_nonempty_empty this

/-- In a discrete solution space every property set is closed, so the
closedness hypotheses above are vacuous.  Carlson 2012 works over
finite (hence discrete-topologizable) spaces of keys and messages. -/
theorem isClosed_feasibilitySet_of_discrete [DiscreteTopology Ξ]
    (S : I → Set Ξ) :
    IsClosed (feasibilitySet S) :=
  isClosed_discrete _

/-- A singleton feasibility set is closed in a T1 space; idealness is
therefore topologically stable there (the constraint "be the truth" is
itself a closed property). -/
theorem Ideal.isClosed_feasibilitySet [T1Space Ξ] {S : I → Set Ξ} {h : Ξ}
    (hi : Ideal S h) : IsClosed (feasibilitySet S) := by
  rw [hi]
  exact isClosed_singleton

end STE
