/-
The Helly / consistency-number structure: a metric-free discriminator
between constraint families whose local (small-subfamily) agreement
already forces global feasibility, and families where it does not.

`Ste.FiniteInstance` showed that a *frame* corpus (`frameConstraint`,
one author fixing a partial assignment `frame a : V → Option W`) reduces
global feasibility to the PAIRWISE check `Consistent`
(`nonempty_iff_consistent`).  This file promotes that fact to its proper
combinatorial name: a frame corpus has **Helly number 2** -- checking
every PAIR of authors already certifies the whole corpus.  This is the
same phenomenon classically captured by Helly's theorem for convex sets
in `ℝ^d` (every `d+1`-wise intersecting family of convex sets is
globally intersecting) and by the tree-width-1 / acyclic-hypergraph
"local consistency implies global consistency" theorems of constraint
satisfaction (Beeri--Fagin--Maier--Yannakakis, Dechter's arc-consistency
tractability results, mechanized elsewhere in this repo as
`Ste.ConsistencyTree`).  Here the discriminator is *structural*
(rectangularity of `frameConstraint`, `Ste.FrameRectangular`), not
metric or convexity-based, matching the "metric-free" character of the
rest of the STE mechanization.

We also record, as a witness that Helly-2 is a genuine structural
property and not a triviality of finite index sets, the classical
3-set counterexample: three sets, pairwise intersecting, with empty
global intersection (`exists_not_hasHelly_two`).  This is exactly the
`d = 1`, `k = 3` failure of Helly's theorem (three intervals'
worth-of-structure in a non-convex setting) and shows why frame corpora
-- which avoid it via rectangularity -- are structurally special.

Reference: P. L. Combettes, "The Foundations of Set Theoretic
Estimation," Proc. IEEE 81(2), 1993 (for `feasibilitySet` /
`partialFeasibilitySet`, mechanized in `Ste.Basic`); the classical Helly
theorem (E. Helly, 1923) for the naming convention.
-/
import Ste.Basic
import Ste.FiniteInstance
import Ste.FrameRectangular

namespace STE

open Set

variable {Ξ I : Type*}

/-! ### k-wise consistency and the Helly property -/

/-- **`k`-wise consistency**: every subfamily of at most `k` property
sets already has a nonempty (partial) intersection.  The finite-subset
analogue of `feasibilitySet`/`partialFeasibilitySet` nonemptiness
(`Ste.Basic`), and the hypothesis side of a Helly-type theorem. -/
def KWiseConsistent (S : I → Set Ξ) (k : ℕ) : Prop :=
  ∀ J : Finset I, J.card ≤ k → (⋂ i ∈ J, S i).Nonempty

/-- **The Helly property at level `k`**: `k`-wise consistency of a
family already forces its full feasibility set to be nonempty. This is
the "consistency number `≤ k`" property -- checking subfamilies of size
`k` is a complete feasibility test. -/
def HasHelly (S : I → Set Ξ) (k : ℕ) : Prop :=
  KWiseConsistent S k → (feasibilitySet S).Nonempty

/-- `k`-wise consistency is antitone in `k`: demanding consistency of
MORE subfamilies (larger `k`) is a stronger hypothesis, so it implies
consistency at every smaller level. -/
theorem KWiseConsistent.mono {S : I → Set Ξ} {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    (h : KWiseConsistent S k₂) : KWiseConsistent S k₁ :=
  fun J hJ => h J (hJ.trans hk)

/-- A finite subfamily's intersection, read via the Finset-indexed
`⋂ i ∈ J, S i` notation, coincides with `partialFeasibilitySet` on the
coerced index set `↑J`. -/
theorem partialFeasibilitySet_coe_finset (S : I → Set Ξ) (J : Finset I) :
    partialFeasibilitySet S (↑J : Set I) = ⋂ i ∈ J, S i := by
  ext a
  simp only [partialFeasibilitySet, Set.mem_iInter, Finset.mem_coe]

/-- **Global consistency implies `k`-wise consistency for every `k`.**
A nonempty feasibility set already witnesses every finite subfamily's
nonemptiness, since enforcing all constraints refines enforcing any
subcollection of them (`feasibilitySet_subset_partial`,
`Ste.Basic`). -/
theorem kWiseConsistent_of_feasibilitySet_nonempty {S : I → Set Ξ}
    (h : (feasibilitySet S).Nonempty) (k : ℕ) :
    KWiseConsistent S k := by
  intro J _
  rw [← partialFeasibilitySet_coe_finset]
  exact h.mono (feasibilitySet_subset_partial S (↑J : Set I))

/-- Global consistency trivially satisfies `HasHelly` at every level: the
conclusion holds outright, independent of the `k`-wise hypothesis. -/
theorem hasHelly_of_feasibilitySet_nonempty {S : I → Set Ξ}
    (h : (feasibilitySet S).Nonempty) (k : ℕ) : HasHelly S k :=
  fun _ => h

/-! ### Frame corpora are Helly-2 -/

variable {A V W : Type*}

/-- Every author's frame constraint is nonempty: extend the fixed values
with an arbitrary background reading (`Inhabited W` picks it). Recorded
as a standalone fact about `frameConstraint`; `frame_hasHelly_two` below
does not need it separately since its uniform `{a, b}`-pair argument
already covers the `a = b` case. -/
theorem frameConstraint_nonempty [Inhabited W] (frame : A → V → Option W)
    (a : A) : (frameConstraint frame a).Nonempty :=
  ⟨fun v => (frame a v).getD default, fun v x hx => by simp [hx]⟩

/-- **Frame corpora have Helly number 2 (the headline).** If every PAIR
of authors is jointly satisfiable, the WHOLE corpus is. Proof route:
`KWiseConsistent (frameConstraint frame) 2` applied to `{a, b}`
(`Finset.card_le_two`) gives, for every pair of authors, an assignment
in both their property sets; `compatibleOn_of_mem` turns this into
pairwise `compatibleOn`, hence `Consistent frame`
(`Ste.FiniteInstance`), hence the feasibility set is nonempty
(`nonempty_of_consistent`). This says frame corpora have *consistency
number* 2: pairwise consistency already certifies global consistency,
exactly like Helly's theorem for convex sets in the line (`d = 1`,
Helly number `d + 1 = 2`). -/
theorem frame_hasHelly_two [Fintype A] [DecidableEq A] [Fintype V]
    [DecidableEq W] [Inhabited W] (frame : A → V → Option W) :
    HasHelly (frameConstraint frame) 2 := by
  intro h2
  refine nonempty_of_consistent (frame := frame) ?_
  intro v a b
  have hab : (⋂ i ∈ ({a, b} : Finset A), frameConstraint frame i).Nonempty :=
    h2 {a, b} Finset.card_le_two
  obtain ⟨f, hf⟩ := hab
  rw [Set.mem_iInter₂] at hf
  have ha : f ∈ frameConstraint frame a := hf a (Finset.mem_insert_self a {b})
  have hb : f ∈ frameConstraint frame b :=
    hf b (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
  exact compatibleOn_of_mem ha hb

/-! ### Helly-2 fails in general (the discriminator) -/

/-- **The classical 3-set Helly failure**, witnessing that Helly-2 is a
genuine structural property and not automatic: three subsets of
`Fin 3`, pairwise intersecting (each pairwise intersection is a
singleton, so `KWiseConsistent · 2` holds), yet with EMPTY global
intersection. This is exactly the discriminator that separates frame
corpora (`frame_hasHelly_two`, always Helly-2) from constraint families
in general -- "pairwise ⟹ global" is a special property, not a
tautology of finite index sets. -/
private def hellyFailureFamily : Fin 3 → Set (Fin 3)
  | 0 => {0, 1}
  | 1 => {1, 2}
  | 2 => {0, 2}

theorem exists_not_hasHelly_two :
    ∃ S : Fin 3 → Set (Fin 3), KWiseConsistent S 2 ∧
      ¬ (feasibilitySet S).Nonempty := by
  refine ⟨hellyFailureFamily, ?_, ?_⟩
  · intro J hJ
    fin_cases J <;> simp_all [hellyFailureFamily] <;>
      first
        | exact ⟨0, by decide⟩
        | exact ⟨1, by decide⟩
        | exact ⟨2, by decide⟩
  · rw [Set.not_nonempty_iff_eq_empty]
    ext a
    simp only [feasibilitySet, Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
    intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    simp [hellyFailureFamily] at h0 h1 h2
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      simp_all

/-! ### The feasibility closure structure -/

/-- The closure of `X` under the property-set family `S`: the
intersection of every property set that already contains `X`. The
smallest `S`-closed set containing `X` -- a Moore closure generated by
the family `{S i}`. -/
def cl (S : I → Set Ξ) (X : Set Ξ) : Set Ξ :=
  partialFeasibilitySet S {i | X ⊆ S i}

/-- **Extensivity**: `X` lies inside its own closure. Every generator
`S i` containing `X` still contains `X`, so their intersection does
too. -/
theorem cl_extensive (S : I → Set Ξ) (X : Set Ξ) : X ⊆ cl S X := by
  intro x hx
  simp only [cl, partialFeasibilitySet, Set.mem_iInter, Set.mem_setOf_eq]
  exact fun i hi => hi hx

/-- **Monotonicity**: closure preserves containment. A direct
consequence of `partialFeasibilitySet_antitone` (`Ste.Basic`): the
larger set `Y` is contained in fewer generators, so its closure is an
intersection over a smaller index set, hence bigger. -/
theorem cl_monotone (S : I → Set Ξ) {X Y : Set Ξ} (hXY : X ⊆ Y) :
    cl S X ⊆ cl S Y :=
  partialFeasibilitySet_antitone S (fun _ hi => hXY.trans hi)

/-- Every generator `S i` containing `X` also contains the closure of
`X` -- the closure is the intersection of exactly those generators, so
it refines each one. -/
theorem cl_subset_of_subset {S : I → Set Ξ} {X : Set Ξ} {i : I}
    (hi : X ⊆ S i) : cl S X ⊆ S i := by
  simp only [cl, partialFeasibilitySet]
  exact Set.biInter_subset_of_mem hi

/-- **Idempotence**: closing twice does nothing new. `⊇` is
`cl_extensive`; `⊆` holds because every generator containing `X` also
contains `cl S X` (`cl_subset_of_subset`), so the generators available
to close `cl S X` are at least those available to close `X`, giving
`cl S (cl S X) ⊆ cl S X`. -/
theorem cl_idempotent (S : I → Set Ξ) (X : Set Ξ) :
    cl S (cl S X) = cl S X := by
  refine Set.Subset.antisymm ?_ (cl_extensive S (cl S X))
  apply partialFeasibilitySet_antitone
  intro i hi
  exact cl_subset_of_subset hi

/-- A set is `S`-closed when it equals its own closure -- exactly the
sets expressible as an intersection of some subfamily of the generators
`S i`. -/
def IsClClosed (S : I → Set Ξ) (C : Set Ξ) : Prop :=
  cl S C = C

/-- **The closed sets form a Moore family**: closed under arbitrary
intersection. If every `C k` in a (possibly infinite) family is closed,
so is `⋂ k, C k`: it is squeezed between `cl_extensive` from below and,
from above, each `cl S (⋂ k, C k) ⊆ cl S (C k) = C k` by
`cl_monotone`. -/
theorem isClClosed_iInter {K : Type*} (S : I → Set Ξ) (C : K → Set Ξ)
    (hC : ∀ k, IsClClosed S (C k)) : IsClClosed S (⋂ k, C k) := by
  refine Set.Subset.antisymm ?_ (cl_extensive S (⋂ k, C k))
  refine Set.subset_iInter fun k => ?_
  calc cl S (⋂ k, C k) ⊆ cl S (C k) := cl_monotone S (Set.iInter_subset C k)
    _ = C k := hC k

/-! ### Helly-2 and obstruction-freeness are the same "no coupling" -/

/-- **Frame corpora enjoy both facets of "no coupling" at once**: the
consistency-number statement (`frame_hasHelly_two`, pairwise consistency
implies global) and the cohomological statement
(`frame_cechVanishesCover`, `Ste.FrameRectangular`: every cover's Čech
obstruction vanishes). Both are downstream of the same structural fact
-- a frame corpus's feasibility set is a rectangle
(`isRectangle_feasibilitySet_frame`), so it carries no cross-variable
coupling for either a combinatorial (Helly) or a topological (Čech) test
to detect. -/
theorem frame_hasHelly_two_and_cechVanishesCover [Fintype A] [DecidableEq A]
    [Fintype V] [DecidableEq W] [Inhabited W] (frame : A → V → Option W) {J : Type*}
    (U : J → Set V) (hcover : ∀ v, ∃ j, v ∈ U j) :
    HasHelly (frameConstraint frame) 2 ∧
      CechVanishesCover (feasibilitySet (frameConstraint frame)) U :=
  ⟨frame_hasHelly_two frame, frame_cechVanishesCover frame U hcover⟩

end STE
