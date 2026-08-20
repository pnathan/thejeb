/-
Plural feasible sets: a crisp specialization of Jøsang-style
hyperopinions to set theoretic estimation.

In the ordinary STE setting each source `i` contributes a single
property set `S i ⊆ Ξ`.  A *hyper* source is less committal: it offers a
collection `H i : Set (Set Ξ)` of alternative property sets, asserting
only that the truth lies in one of them.  The information carried by
such a source is therefore the union `⋃ S ∈ H i, S`.

The main result is that the plural feasibility set — the intersection of
the per-source unions — decomposes as the union, over all *choices* of
one branch per source, of the ordinary STE feasibility sets.  That is,
plural feasibility is exactly "some consistent selection of branches".
-/
import Mathlib.Data.Set.Lattice

namespace STE.PluralFeasibility

variable {Ξ ι : Type*} (H : ι → Set (Set Ξ))

/-- The information carried by a hyper source: the union of the
alternative property sets it offers. -/
def hyperInfo (i : ι) : Set Ξ := ⋃ S ∈ H i, S

/-- **Branch decomposition of plural feasibility**: the intersection of
the hyper informations equals the union, over all selections `σ` of one
branch per source, of the corresponding feasibility sets. -/
theorem iInter_hyperInfo_eq_iUnion_choice :
    ⋂ i, hyperInfo H i = ⋃ σ : ∀ i, H i, ⋂ i, (σ i : Set Ξ) := by
  ext a
  constructor
  · intro ha
    simp only [Set.mem_iInter, hyperInfo, Set.mem_iUnion, exists_prop] at ha
    choose S hS haS using ha
    exact Set.mem_iUnion.mpr ⟨fun i => ⟨S i, hS i⟩, Set.mem_iInter.mpr haS⟩
  · intro ha
    obtain ⟨σ, hσ⟩ := Set.mem_iUnion.mp ha
    refine Set.mem_iInter.mpr fun i => ?_
    have := Set.mem_iInter.mp hσ i
    exact Set.mem_biUnion (σ i).2 this

/-- Pruning the empty branch does not change what a hyper source says:
an empty alternative contributes nothing to the union. -/
theorem iUnion_sdiff_empty (A : Set (Set Ξ)) :
    ⋃ S ∈ (A \ {∅} : Set (Set Ξ)), S = ⋃ S ∈ A, S := by
  ext a
  simp only [Set.mem_iUnion, Set.mem_diff, Set.mem_singleton_iff, exists_prop]
  constructor
  · rintro ⟨S, ⟨hSA, -⟩, haS⟩
    exact ⟨S, hSA, haS⟩
  · rintro ⟨S, hSA, haS⟩
    exact ⟨S, ⟨hSA, fun h => by simp [h] at haS⟩, haS⟩

end STE.PluralFeasibility
