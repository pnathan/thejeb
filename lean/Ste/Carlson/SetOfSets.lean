/-
A SECOND-ORDER extension of Carlson-style set theoretic estimation:
sources that contribute not a single possibility set but a SET OF
POSSIBILITY SETS.

`Ste.HellyConsistency` mechanizes the first-order picture: a source
`i` (an author, a piece of evidence, a Carlson decryption constraint)
contributes one property set `S i ⊆ Ξ`, and frame corpora enjoy Helly
number 2 (`frame_hasHelly_two`): pairwise consistency of the property
sets already certifies global consistency.

Here we model a source that is *uncertain about its own possibility
set*: a candidate decryption, or a document under interpretive dispute,
may say "the truth lies in one of THESE possibility sets" rather than
pinning down a single set. Formally each source `i` offers a family
`𝒮 i ⊆ 𝒫(Ξ)` of candidate possibility sets (a `SetFamily`), and a
*selection* is a system of representatives `choice i ∈ 𝒮 i` for a
subfamily `J`. The natural second-order analogue of `k`-wise
consistency (`KWiseSelectable`) asks that EVERY subfamily of size `≤ k`
allow SOME selection with nonempty intersection; the analogue of
`HasHelly` (`HasHellySel`) asks whether that already certifies a
GLOBAL selection with nonempty intersection.

The headline result (`exists_not_hasHellySel_two`) is that this
second-order Helly number is NOT 2: we exhibit three sources, each
offering a two-element family of singleton possibility sets on `Fin 3`,
that are pairwise selectable-consistent (`KWiseSelectable 𝒮 2`) but not
globally selectable-consistent, so `HasHellySel 𝒮 2` fails outright.
This is a genuinely second-order phenomenon: the underlying points
`0, 1, 2` realize the SAME triangle obstruction as
`Ste.HellyConsistency.hellyFailureFamily`, but here it is latent in the
CHOICE structure rather than forced by a single fixed set per source --
exactly the freedom that "a set of possibility sets" adds over "a
possibility set." First-order consistency embeds faithfully as the
special case of a singleton family (`selectable_singleton_iff`), so
this is a strict extension, not merely a relabeling, of
`Ste.HellyConsistency`.

Reference: A. H. Carlson, "Set Theoretic Estimation Applied to the
Information Content of Ciphers and Decryption," Ph.D. dissertation,
University of Idaho, May 2012 (the source-contributes-a-possibility-set
vocabulary); E. Helly, 1923 (the Helly number naming convention, as in
`Ste.HellyConsistency`).
-/
import Ste.HellyConsistency

namespace STE.Carlson

open Set

/-! ### Second-order sources: a set of possibility sets per index -/

/-- A **second-order source family**: index `i` offers a whole set of
CANDIDATE possibility sets `𝒮 i ⊆ 𝒫(Ξ)`, rather than a single fixed
property set. The first-order picture of `Ste.HellyConsistency`
(`S : I → Set Ξ`) is the special case where every `𝒮 i` is a
singleton (`selectable_singleton_iff` below). -/
def SetFamily (Ξ I : Type*) : Type _ := I → Set (Set Ξ)

variable {Ξ I : Type*}

/-- **Selectable consistency**: a subfamily `J` is selectable-consistent
when there is a SYSTEM OF REPRESENTATIVES `choice : I → Set Ξ`, one
candidate possibility set `choice i ∈ 𝒮 i` per source in `J`, whose
intersection is nonempty. This is the second-order analogue of
`(⋂ i ∈ J, S i).Nonempty` (`Ste.HellyConsistency.KWiseConsistent`'s
hypothesis): instead of intersecting the FIXED sets `S i`, we get to
CHOOSE, for each source, which of its candidate sets to intersect. -/
def SelectableConsistent (𝒮 : SetFamily Ξ I) (J : Set I) : Prop :=
  ∃ choice : I → Set Ξ, (∀ i ∈ J, choice i ∈ 𝒮 i) ∧ (⋂ i ∈ J, choice i).Nonempty

/-- **`k`-wise selectable consistency**: every subfamily of at most `k`
sources admits SOME selection with nonempty intersection. The
second-order analogue of `Ste.HellyConsistency.KWiseConsistent`. -/
def KWiseSelectable (𝒮 : SetFamily Ξ I) (k : ℕ) : Prop :=
  ∀ J : Finset I, J.card ≤ k → SelectableConsistent 𝒮 (↑J : Set I)

/-- **The second-order Helly property at level `k`**: `k`-wise
selectable consistency of a second-order source family already forces
a GLOBAL selection with nonempty intersection. The second-order
analogue of `Ste.HellyConsistency.HasHelly`. -/
def HasHellySel (𝒮 : SetFamily Ξ I) (k : ℕ) : Prop :=
  KWiseSelectable 𝒮 k → SelectableConsistent 𝒮 (Set.univ : Set I)

/-- `k`-wise selectable consistency is antitone in `k`, exactly as for
`KWiseConsistent.mono`: demanding a selection for MORE subfamilies
(larger `k`) is a stronger hypothesis. -/
theorem KWiseSelectable.mono {𝒮 : SetFamily Ξ I} {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    (h : KWiseSelectable 𝒮 k₂) : KWiseSelectable 𝒮 k₁ :=
  fun J hJ => h J (hJ.trans hk)

/-- Global selectable consistency trivially satisfies `HasHellySel` at
every level, exactly as `hasHelly_of_feasibilitySet_nonempty`: the
conclusion holds outright, independent of the `k`-wise hypothesis. -/
theorem hasHellySel_of_selectableConsistent_univ {𝒮 : SetFamily Ξ I}
    (h : SelectableConsistent 𝒮 (Set.univ : Set I)) (k : ℕ) : HasHellySel 𝒮 k :=
  fun _ => h

/-! ### The first-order case embeds as the singleton family -/

/-- The second-order family generated by a first-order family `S`: every
source offers exactly ONE candidate possibility set, namely `S i`
itself. -/
def singletonFamily (S : I → Set Ξ) : SetFamily Ξ I := fun i => {S i}

/-- **First-order consistency embeds faithfully.** When every source's
second-order family is a singleton, `SelectableConsistent` collapses to
the ordinary "intersection of the (unique, forced) property sets is
nonempty" -- exactly `Ste.HellyConsistency`'s hypothesis on
`partialFeasibilitySet`/`⋂ i ∈ J, S i`. There is no room for the
CHOICE freedom that drives the headline counterexample below: a
singleton family has only one possible `choice`, namely `choice = S`
itself, forced by membership in a one-element set. -/
theorem selectable_singleton_iff (S : I → Set Ξ) (J : Set I) :
    SelectableConsistent (singletonFamily S) J ↔ (⋂ i ∈ J, S i).Nonempty := by
  constructor
  · rintro ⟨choice, hmem, hne⟩
    have heq : ∀ i ∈ J, choice i = S i := fun i hi =>
      Set.mem_singleton_iff.mp (hmem i hi)
    have hset : (⋂ i ∈ J, choice i) = ⋂ i ∈ J, S i := by
      ext x
      simp only [Set.mem_iInter₂]
      constructor
      · intro h i hi; rw [← heq i hi]; exact h i hi
      · intro h i hi; rw [heq i hi]; exact h i hi
    rwa [hset] at hne
  · rintro ⟨x, hx⟩
    exact ⟨S, fun i _ => rfl, ⟨x, hx⟩⟩

/-- Consequently the second-order `KWiseSelectable` of a singleton
family is exactly the first-order `KWiseConsistent`, and likewise for
`HasHellySel`/`HasHelly` -- the second-order machinery is a genuine
extension, recovering the first-order theory (in particular
`frame_hasHelly_two`) on the nose when there is no set-of-sets
ambiguity to exploit. -/
theorem kWiseSelectable_singletonFamily_iff (S : I → Set Ξ) (k : ℕ) :
    KWiseSelectable (singletonFamily S) k ↔ KWiseConsistent S k := by
  unfold KWiseSelectable STE.KWiseConsistent
  exact forall_congr' fun J => forall_congr' fun _ => selectable_singleton_iff S (↑J : Set I)

theorem hasHellySel_singletonFamily_iff (S : I → Set Ξ) (k : ℕ) :
    HasHellySel (singletonFamily S) k ↔ HasHelly S k := by
  unfold HasHellySel STE.HasHelly
  rw [kWiseSelectable_singletonFamily_iff S k, selectable_singleton_iff S Set.univ,
    Set.biInter_univ]
  rfl

/-! ### The headline: the second-order Helly number exceeds 2 -/

/-- **The set-of-sets Helly-2 failure witness.** Three sources over
`Ξ = Fin 3`, each offering a TWO-element family of singleton candidate
sets:

* source `0` offers `{0}` or `{1}`;
* source `1` offers `{1}` or `{2}`;
* source `2` offers `{2}` or `{0}`.

Any two adjacent sources can agree on the shared point of their two
option-sets (`0`-`1` agree on `1`, `1`-`2` agree on `2`, `2`-`0` agree
on `0`), giving `KWiseSelectable · 2`
(`setOfSetsFailure_kWiseSelectable_two`). But no single point lies in
all three "either-or" pairs simultaneously -- `{0,1} ∩ {1,2} ∩ {2,0}
= ∅`, the same triangle obstruction as
`Ste.HellyConsistency.hellyFailureFamily` -- so no global selection
exists (`setOfSetsFailure_not_selectableConsistent_univ`), and
`HasHellySel · 2` is FALSE (`setOfSetsFailure_not_hasHellySel_two`). -/
private def setOfSetsFailureFamily : SetFamily (Fin 3) (Fin 3)
  | 0 => {({0} : Set (Fin 3)), {1}}
  | 1 => {({1} : Set (Fin 3)), {2}}
  | 2 => {({2} : Set (Fin 3)), {0}}

/-- Every subfamily of at most 2 of the three sources admits a
selection with nonempty intersection: the empty subfamily trivially
(pick anything), each singleton subfamily by picking either candidate
(both are nonempty singletons), and each pair by picking their shared
point. -/
theorem setOfSetsFailure_kWiseSelectable_two :
    KWiseSelectable setOfSetsFailureFamily 2 := by
  intro J hJ
  fin_cases J <;>
    first
      | -- the card-3 case contradicts `hJ : J.card ≤ 2`
        (exfalso; revert hJ; decide)
      | -- ∅: any constant choice works, the biInter is `univ`
        (refine ⟨fun _ => Set.univ, ?_, ?_⟩
         · simp
         · simp [Set.univ_nonempty (α := Fin 3)])
      | -- singletons and pairs: a constant choice at a witness point
        (refine ⟨fun _ => ({0} : Set (Fin 3)), ?_, ?_⟩
         · intro i hi; rw [Finset.mem_coe] at hi; fin_cases hi <;>
             simp [setOfSetsFailureFamily]
         · simp)
      | (refine ⟨fun _ => ({1} : Set (Fin 3)), ?_, ?_⟩
         · intro i hi; rw [Finset.mem_coe] at hi; fin_cases hi <;>
             simp [setOfSetsFailureFamily]
         · simp)
      | (refine ⟨fun _ => ({2} : Set (Fin 3)), ?_, ?_⟩
         · intro i hi; rw [Finset.mem_coe] at hi; fin_cases hi <;>
             simp [setOfSetsFailureFamily]
         · simp)

/-- No selection of the three sources' candidate sets has a common
point: the only choices available are `choice 0 ∈ {0, 1}`,
`choice 1 ∈ {1, 2}`, `choice 2 ∈ {2, 0}` (as points), and
`{0,1} ∩ {1,2} ∩ {2,0} = ∅` in `Fin 3`, checked by the 8-way case
split below. -/
theorem setOfSetsFailure_not_selectableConsistent_univ :
    ¬ SelectableConsistent setOfSetsFailureFamily (Set.univ : Set (Fin 3)) := by
  rintro ⟨choice, hmem, x, hx⟩
  have h0 := hmem 0 (Set.mem_univ 0)
  have h1 := hmem 1 (Set.mem_univ 1)
  have h2 := hmem 2 (Set.mem_univ 2)
  simp only [setOfSetsFailureFamily, Set.mem_insert_iff, Set.mem_singleton_iff] at h0 h1 h2
  have hx' : ∀ i, x ∈ choice i := by simpa only [Set.mem_iInter₂, Set.mem_univ, true_implies] using hx
  have hx0 := hx' 0
  have hx1 := hx' 1
  have hx2 := hx' 2
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    rw [h0] at hx0 <;> rw [h1] at hx1 <;> rw [h2] at hx2 <;>
    simp only [Set.mem_singleton_iff] at hx0 hx1 hx2 <;>
    first
      | exact absurd (hx0.symm.trans hx1) (by decide)
      | exact absurd (hx0.symm.trans hx2) (by decide)

/-- The headline second-order Helly-2 failure: this witness's
second-order family is pairwise (indeed `k = 2`-wise) selectable
consistent yet has no globally selectable-consistent choice, so
`HasHellySel · 2` fails outright. Contrast with `frame_hasHelly_two`:
first-order frame corpora ALWAYS have Helly number `2`; the second-order
set-of-sets extension does not inherit this, exhibiting the strict
increase in Helly number the set-of-sets generalization introduces. -/
theorem setOfSetsFailure_not_hasHellySel_two : ¬ HasHellySel setOfSetsFailureFamily 2 :=
  fun h => setOfSetsFailure_not_selectableConsistent_univ
    (h setOfSetsFailure_kWiseSelectable_two)

/-- **The headline theorem**: the second-order Helly number of set-of-sets
consistency strictly exceeds `2`, in contrast to the first-order
`frame_hasHelly_two`. There is a second-order source family that is
`2`-wise selectable consistent (in particular, pairwise) but for which
`HasHellySel · 2` fails -- so `k = 2` is NOT a Helly number for the
selectable-consistency notion in general, unlike the first-order
frame case. -/
theorem exists_not_hasHellySel_two :
    ∃ 𝒮 : SetFamily (Fin 3) (Fin 3), KWiseSelectable 𝒮 2 ∧ ¬ HasHellySel 𝒮 2 :=
  ⟨setOfSetsFailureFamily, setOfSetsFailure_kWiseSelectable_two,
    setOfSetsFailure_not_hasHellySel_two⟩

/-! ### General remark

`exists_not_hasHellySel_two` proves the second-order Helly number is
`≥ 3` on the nose: `HasHellySel · 2` is refuted by an explicit witness,
so no proof of "`k = 2`-wise selectable consistency implies global
selectable consistency" can hold in general for `SetFamily`, in sharp
contrast to `frame_hasHelly_two`'s unconditional first-order Helly-2
guarantee. Whether allowing each source to offer LARGER option
families (more than two candidate sets, as here) or MORE sources can
force the second-order Helly number arbitrarily high is a natural
further question that this file does not settle; we record only what
`exists_not_hasHellySel_two` establishes: the number is strictly more
than `2`, i.e. at least `3`. -/

end STE.Carlson
