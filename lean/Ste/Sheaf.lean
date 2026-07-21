/-
Representation and tractability of set theoretic estimation: gluing,
rectangular bounds, and the coupling obstruction.

The feasible set lives in `Set Ξ` with `|Ξ|` typically exponential (the
`2^N` wall of the dynamic-frame solver).  When can it be represented
*locally* and glued, avoiding the blow-up?  This is a sheaf-theoretic
question.

* **Gluing (sheaf on the constraint side).**  `feasibilitySet` sends a
  union cover of the constraint index to the *intersection* of the local
  feasible sets (`feasibilitySet_eq_iInter_cover`).  So the presheaf
  `J ↦ feas(J)` takes colimits of constraints to limits of feasible sets
  — it is a sheaf for union-coverage, and no obstruction lives here.

* **Tractable upper bound (rectangular constraints).**  Model the
  hypothesis space as a product `Ξ = ∀ v, A v` (variables/claims).  If
  every constraint is *rectangular* (`S i = univ.pi (P i)`, i.e. depends
  on each variable separately), the feasible set is itself a rectangle
  `univ.pi (fun v => ⋂ i, P i v)` (`rectangular_feasibilitySet`).  It is
  then representable in `∑ v` space (one subset per variable) with
  `encard = ∏ v, |⋂ i, P i v|` (`rectangular_encard`) — no exponential.

* **The obstruction (lower bound).**  A single *coupling* constraint —
  the diagonal `{f | f 0 = f 1}` on two binary variables — is provably
  NOT rectangular (`diagonal_not_rectangular`).  Hence no per-variable
  representation exists: variable coupling is the exact source of
  intractability.  This non-rectangularity is the elementary shape of
  Abramsky-style contextuality / a nonzero Čech gluing obstruction, and
  the same shape as `Ste.DynamicFrame.Counterexample` (non-transitive
  possible-coreference).

References: S. Abramsky, A. Brandenburger, *The sheaf-theoretic structure
of non-locality and contextuality*, 2011; B. Ganter, R. Wille, *Formal
Concept Analysis*, 1999; Combettes 1993.
-/
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases
import Ste.HyperFrame

namespace STE

open Order Set

variable {Ξ : Type*} {I : Type*} (S : I → Set Ξ)

/-! ### Gluing: the constraint-side sheaf condition -/

/-- Feasibility distributes over any union of constraint sets: the
feasible set of a union of constraints is the intersection of the local
feasible sets.  This is `lowerPolar_iUnion` for the STE context. -/
theorem partialFeasibilitySet_iUnion {κ : Type*} (𝒥 : κ → Set I) :
    partialFeasibilitySet S (⋃ k, 𝒥 k)
      = ⋂ k, partialFeasibilitySet S (𝒥 k) := by
  rw [partialFeasibilitySet_eq_lowerPolar, lowerPolar_iUnion]
  simp_rw [← partialFeasibilitySet_eq_lowerPolar]

/-- **Gluing / sheaf condition.**  For any cover `⋃ k, 𝒥 k = univ` of the
constraint index, the global feasible set is the limit (intersection) of
the local feasible sets.  Local sections glue to a global one. -/
theorem feasibilitySet_eq_iInter_cover {κ : Type*} (𝒥 : κ → Set I)
    (hcover : ⋃ k, 𝒥 k = Set.univ) :
    feasibilitySet S = ⋂ k, partialFeasibilitySet S (𝒥 k) := by
  rw [← partialFeasibilitySet_univ, ← hcover, partialFeasibilitySet_iUnion]

/-! ### Tractable upper bound: rectangular (variable-separable) constraints -/

section Product

variable {V : Type*} {A : V → Type*}

/-- **Rectangular representation.**  If every constraint is a product
(cylinder) `univ.pi (P i)`, the feasible set is the rectangle whose
`v`-th side is the pointwise intersection `⋂ i, P i v`.  Thus a
variable-separable STE problem is represented by one subset per variable
(`∑ v` space), never the `∏ v` product. -/
theorem rectangular_feasibilitySet (P : I → ∀ v, Set (A v)) :
    feasibilitySet (fun i => Set.univ.pi (P i))
      = Set.univ.pi (fun v => ⋂ i, P i v) := by
  ext f
  simp only [feasibilitySet, Set.mem_iInter, Set.mem_univ_pi]
  exact ⟨fun h v i => h i v, fun h i v => h v i⟩

/-- **Representation bound.**  Over finitely many variables, the feasible
set of rectangular constraints has cardinality the product of the local
feasible cardinalities — the exact tractable-case size formula. -/
theorem rectangular_encard [Fintype V] (P : I → ∀ v, Set (A v)) :
    (feasibilitySet (fun i => Set.univ.pi (P i))).encard
      = ∏ v, (⋂ i, P i v).encard := by
  rw [rectangular_feasibilitySet]
  exact Set.encard_pi_eq_prod_encard

end Product

/-! ### The coupling obstruction (representation lower bound) -/

/-- The diagonal (coupling) constraint on two binary variables: the two
bits must agree. -/
def diagonal : Set (Fin 2 → Bool) := {f | f 0 = f 1}

/-- **Coupling is not rectangular.**  The diagonal constraint is not a
product `univ.pi t` for any per-variable side family `t`: a rectangle
containing `(0,0)` and `(1,1)` must contain `(0,1)`, which violates the
coupling.  Hence variable-coupling constraints admit no per-variable
(linear) representation — the elementary contextuality obstruction and
the source of the `2^N` wall. -/
theorem diagonal_not_rectangular :
    ¬ ∃ t : Fin 2 → Set Bool, diagonal = Set.univ.pi t := by
  rintro ⟨t, ht⟩
  have h00 : (fun _ => false) ∈ diagonal := rfl
  have h11 : (fun _ => true) ∈ diagonal := rfl
  rw [ht, Set.mem_univ_pi] at h00 h11
  have hf0 : false ∈ t 0 := by simpa using h00 0
  have ht1 : true ∈ t 1 := by simpa using h11 1
  -- the mixed point (false, true)
  have hmix : (fun v : Fin 2 => decide (v = 1)) ∈ Set.univ.pi t := by
    rw [Set.mem_univ_pi]
    intro v
    fin_cases v
    · simpa using hf0
    · simpa using ht1
  rw [← ht] at hmix
  exact absurd
    (show decide ((0 : Fin 2) = 1) = decide ((1 : Fin 2) = 1) from hmix)
    (by decide)

/-! ### The quantitative gap: 2 solutions, but rectangular hull of size 4 -/

/-- The diagonal consists of exactly the two constant assignments. -/
theorem diagonal_eq_pair :
    diagonal = ({fun _ => false, fun _ => true} : Set (Fin 2 → Bool)) := by
  ext f
  simp only [diagonal, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · intro hf
    have hconst : f = fun _ => f 0 := funext fun v => by
      fin_cases v
      · rfl
      · exact hf.symm
    cases h0 : f 0
    · exact Or.inl (by rw [hconst, h0])
    · exact Or.inr (by rw [hconst, h0])
  · rintro (rfl | rfl) <;> rfl

/-- The coupling constraint has exactly two solutions. -/
theorem diagonal_encard : diagonal.encard = 2 := by
  rw [diagonal_eq_pair]
  exact Set.encard_pair (fun h => by simpa using congrFun h 0)

/-- Any rectangle containing the diagonal is the whole space: the best
rectangular over-approximation of a coupling constraint carries zero
information. -/
theorem rectangle_superset_diagonal_eq_univ (t : Fin 2 → Set Bool)
    (h : diagonal ⊆ Set.univ.pi t) : Set.univ.pi t = Set.univ := by
  have h00 := h (show (fun _ => false) ∈ diagonal from rfl)
  have h11 := h (show (fun _ => true) ∈ diagonal from rfl)
  rw [Set.mem_univ_pi] at h00 h11
  ext f
  simp only [Set.mem_univ_pi, Set.mem_univ, iff_true]
  intro v
  cases hv : f v
  · exact h00 v
  · exact h11 v

/-- The two-bit hypothesis space has four points. -/
theorem encard_univ_two_bits :
    (Set.univ : Set (Fin 2 → Bool)).encard = 4 := by
  rw [Set.encard_univ, ENat.card_eq_coe_fintype_card,
    show Fintype.card (Fin 2 → Bool) = 4 from by decide]
  simp

/-- **Quantitative obstruction gap.**  The diagonal has `encard 2`, but
every rectangle containing it has `encard 4`: the tightest per-variable
(linear) representation of a coupling constraint overshoots the true
feasible set by a factor of two.  Together with `diagonal_encard` this
measures the cost of forgetting the coupling. -/
theorem rectangle_superset_diagonal_encard (t : Fin 2 → Set Bool)
    (h : diagonal ⊆ Set.univ.pi t) : (Set.univ.pi t).encard = 4 := by
  rw [rectangle_superset_diagonal_eq_univ t h, encard_univ_two_bits]

end STE
