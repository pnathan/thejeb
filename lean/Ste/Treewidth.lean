/-
Cut elimination and treewidth-style bounds.

`Ste.Conditioning` mechanized the elimination *step* (conditioning
removes a variable from every scope) and dissolved the two-variable
coupling core.  This file proves the **general** cut-elimination
theorem over an abstract variable type, and the scope accounting that
underlies treewidth bounds.

The two accounting facts behind treewidth:

* **Join unions scopes** (`HasSupport.inter_union`, `HasSupport.iInter`):
  intersecting constraints unions their supports.  Eliminating a
  variable then removes it (`HasSupport.condition`).  So the scope of an
  intermediate table in variable elimination is the union of the joined
  scopes minus the eliminated variable — the "bag" of the elimination.

* **Cut elimination** (`cut_elimination`): if two constraints share only
  a cut variable `v` (`σ ∩ τ ⊆ {v}`), conditioning on `v` yields
  constraints with *disjoint* scopes `σ \ {v}` and `τ \ {v}` — the
  problem falls apart into independent blocks (cf.
  `feasibilitySet_blockFamily`).  This is the general form of the
  two-variable dissolution proved for `diagonal` in `Ste.Conditioning`.

The quantitative bag bound — a `σ`-supported table has at most
`∏ v ∈ σ, |A v|` rows, so an elimination order of width `w` never
materializes a table larger than `a^{w+1}` — is developed on top of
`HasSupport` (see `bag_encard_le` / outlook in the notes).

Reference: R. Dechter, *Constraint Processing*, 2003 (bucket elimination,
induced width); N. Robertson, P. D. Seymour, treewidth.
-/
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sets
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Ste.Conditioning

namespace STE

open Set

variable {V : Type*} {A : V → Type*} [DecidableEq V]

/-- **Join unions scopes.**  Intersecting a constraint supported on `σ`
with one supported on `τ` gives a constraint supported on `σ ∪ τ`: the
scope of a join is the union of the joined scopes. -/
theorem HasSupport.inter_union {T U : Set (∀ v, A v)} {σ τ : Set V}
    (hT : HasSupport T σ) (hU : HasSupport U τ) :
    HasSupport (T ∩ U) (σ ∪ τ) :=
  (hT.mono Set.subset_union_left).inter (hU.mono Set.subset_union_right)

/-- **Join of a family unions all scopes.**  The feasible set of a family
whose `i`-th constraint is supported on `σ i` is supported on `⋃ i, σ i`
— the induced scope of the whole join. -/
theorem HasSupport.iInter {ι : Type*} {T : ι → Set (∀ v, A v)}
    {σ : ι → Set V} (h : ∀ i, HasSupport (T i) (σ i)) :
    HasSupport (⋂ i, T i) (⋃ i, σ i) := by
  intro f g hfg
  simp only [Set.mem_iInter]
  exact forall_congr' fun i => (h i).mono (Set.subset_iUnion σ i) f g hfg

/-- Conditioning distributes over intersection: eliminating a variable
commutes with joining constraints. -/
theorem condition_inter (T U : Set (∀ v, A v)) (v : V) (a : A v) :
    condition (T ∩ U) v a = condition T v a ∩ condition U v a :=
  Set.preimage_inter

/-- After conditioning, two constraints sharing only the cut variable
have disjoint scopes. -/
theorem sdiff_disjoint_of_cut {σ τ : Set V} {v : V} (hcut : σ ∩ τ ⊆ {v}) :
    Disjoint (σ \ {v}) (τ \ {v}) := by
  rw [Set.disjoint_left]
  rintro w ⟨hwσ, hwv⟩ ⟨hwτ, _⟩
  exact hwv (hcut ⟨hwσ, hwτ⟩)

/-- **Cut elimination (general form).**  If constraints `T` and `U` share
only a cut variable `v` (their scopes meet in at most `{v}`), then
conditioning on `v` yields two constraints with *disjoint* scopes
`σ \ {v}` and `τ \ {v}`.  Fixing a cut variable disconnects the
constraint hypergraph into independent blocks — the abstract
variable-elimination step behind bucket elimination and the treewidth
recurrence.  Specializes to the `diagonal` dissolution in
`Ste.Conditioning`. -/
theorem cut_elimination {T U : Set (∀ v, A v)} {σ τ : Set V} (v : V)
    (a : A v) (hT : HasSupport T σ) (hU : HasSupport U τ)
    (hcut : σ ∩ τ ⊆ {v}) :
    HasSupport (condition T v a) (σ \ {v})
      ∧ HasSupport (condition U v a) (τ \ {v})
      ∧ Disjoint (σ \ {v}) (τ \ {v}) :=
  ⟨hT.condition v a, hU.condition v a, sdiff_disjoint_of_cut hcut⟩

/-! ### The bag table and its size bound -/

/-- The **table** of a constraint on the scope `σ`: the image of `T`
under restriction to the coordinates in `σ`.  This is the "relation
table" bucket elimination materializes for a bag. -/
def table (σ : Set V) (T : Set (∀ v, A v)) : Set (∀ v : σ, A (v : V)) :=
  (fun f (v : σ) => f v) '' T

/-- **A supported constraint is its table.**  If `T` has support `σ`,
then `T` is exactly the preimage of its `σ`-table: the table is a
*faithful* representation, losing no information.  Combined with
`table_encard_le` this says a scope-`σ` constraint is representable in
`∏ v ∈ σ, |A v|` rows. -/
theorem HasSupport.eq_preimage_table {T : Set (∀ v, A v)} {σ : Set V}
    (hT : HasSupport T σ) :
    T = (fun f (v : σ) => f v) ⁻¹' table σ T := by
  ext f
  simp only [Set.mem_preimage, table, Set.mem_image]
  constructor
  · intro hf
    exact ⟨f, hf, rfl⟩
  · rintro ⟨g, hg, hgf⟩
    exact (hT g f fun v hv => congrFun hgf ⟨v, hv⟩).mp hg

/-- **The bag bound.**  The table of any constraint on a finite scope
`σ` has at most `∏ v ∈ σ, |A v|` rows — the number of assignments to
the bag.  This is the per-step space cost of bucket elimination. -/
theorem table_encard_le (σ : Set V) [Fintype σ] [∀ v, Fintype (A v)]
    (T : Set (∀ v, A v)) :
    (table σ T).encard ≤ ∏ v : σ, (Fintype.card (A (v : V)) : ℕ∞) := by
  have h1 : (table σ T).encard
      ≤ (Set.univ : Set (∀ v : σ, A (v : V))).encard :=
    Set.encard_mono (Set.subset_univ _)
  rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_pi,
    Nat.cast_prod] at h1
  exact h1

/-- **The uniform bag bound.**  Over alphabets of size at most `k ≥ 1`,
a bag of at most `w + 1` variables has a table of at most `k ^ (w + 1)`
rows: the `a^{w+1}` cost of induced width `w`. -/
theorem table_encard_le_pow (σ : Set V) [Fintype σ] [∀ v, Fintype (A v)]
    (T : Set (∀ v, A v)) {k w : ℕ} (hk : 0 < k)
    (halpha : ∀ u : V, Fintype.card (A u) ≤ k)
    (hbag : Fintype.card σ ≤ w + 1) :
    (table σ T).encard ≤ ((k ^ (w + 1) : ℕ) : ℕ∞) := by
  refine le_trans (table_encard_le σ T) ?_
  rw [← Nat.cast_prod]
  refine ENat.coe_le_coe.mpr (le_trans ?_ (Nat.pow_le_pow_right hk hbag))
  rw [← Finset.card_univ]
  exact Finset.prod_le_pow_card _ _ _ fun x _ => halpha x.1

/-! ### The elimination step: the per-bag invariant of bucket elimination -/

/-- **The elimination step of bucket elimination.**  Join a family of
constraints with scopes `σ i` and eliminate the variable `v`.  The
resulting constraint (i) lives on the *bag*
`(⋃ i, σ i) \ {v}` — the union of the joined scopes minus the
eliminated variable, (ii) is faithfully represented by its table on
the bag, and (iii) if the bag has at most `w + 1` variables
(elimination width `w`) over alphabets of size at most `k > 0`, that
table has at most `k ^ (w + 1)` rows.  This is the per-step space
invariant whose maximum over an elimination order is the induced-width
cost `a^{w+1}` of variable elimination. -/
theorem elimination_step {ι : Type*} {T : ι → Set (∀ v, A v)}
    {σ : ι → Set V} (h : ∀ i, HasSupport (T i) (σ i)) (v : V) (a : A v)
    [Fintype ((⋃ i, σ i) \ {v} : Set V)] [∀ u, Fintype (A u)]
    {k w : ℕ} (hk : 0 < k) (halpha : ∀ u : V, Fintype.card (A u) ≤ k)
    (hbag : Fintype.card ((⋃ i, σ i) \ {v} : Set V) ≤ w + 1) :
    HasSupport (condition (⋂ i, T i) v a) ((⋃ i, σ i) \ {v})
      ∧ condition (⋂ i, T i) v a
          = (fun f (u : ((⋃ i, σ i) \ {v} : Set V)) => f u) ⁻¹'
              table ((⋃ i, σ i) \ {v}) (condition (⋂ i, T i) v a)
      ∧ (table ((⋃ i, σ i) \ {v}) (condition (⋂ i, T i) v a)).encard
          ≤ ((k ^ (w + 1) : ℕ) : ℕ∞) :=
  ⟨(HasSupport.iInter h).condition v a,
    ((HasSupport.iInter h).condition v a).eq_preimage_table,
    table_encard_le_pow _ _ hk halpha hbag⟩

/-! ### The elimination-order total-space bound

`elimination_step` bounds ONE bucket.  The global statement of bucket
elimination is about a whole elimination ORDER: `n` buckets of width
`w` cost at most `n · a^{w+1}` total table space.  We present an order
by the list of its bags. -/

/-- **Bag bound, `Finset` scope.**  Over alphabets of size at most `k`,
a bag given as a `Finset` of at most `w + 1` variables tables any
constraint in at most `k ^ (w + 1)` rows. -/
theorem table_encard_le_pow_finset (σ : Finset V) [∀ u, Fintype (A u)]
    (T : Set (∀ v, A v)) {k w : ℕ} (hk : 0 < k)
    (halpha : ∀ u : V, Fintype.card (A u) ≤ k)
    (hbag : σ.card ≤ w + 1) :
    (table (↑σ : Set V) T).encard ≤ ((k ^ (w + 1) : ℕ) : ℕ∞) := by
  refine table_encard_le_pow (↑σ : Set V) T hk halpha ?_
  calc Fintype.card (↑σ : Set V)
      = σ.card := (Fintype.card_congr
        (Equiv.subtypeEquivRight fun u => Finset.mem_coe)).trans
        (Fintype.card_coe σ)
    _ ≤ w + 1 := hbag

/-- **The elimination-order total-space bound.**  An elimination order
of width `w` presents its buckets as a list `bags` of bags, each of at
most `w + 1` variables.  Over alphabets of size at most `k`, the total
capacity of all bag tables — `∏ v ∈ σ, |A v|` rows for bag `σ`, the
per-bag bound of `table_encard_le` — is at most
`bags.length * k ^ (w + 1)`: bucket elimination along an order of
width `w` runs in `n · a^{w+1}` total table space. -/
theorem elimination_order_total_bound [∀ u, Fintype (A u)]
    (bags : List (Finset V)) {k w : ℕ} (hk : 0 < k)
    (halpha : ∀ u : V, Fintype.card (A u) ≤ k)
    (hwidth : ∀ σ ∈ bags, σ.card ≤ w + 1) :
    (bags.map fun σ => ∏ v ∈ σ, Fintype.card (A v)).sum
      ≤ bags.length * k ^ (w + 1) := by
  have hbound : ∀ x ∈ bags.map fun σ => ∏ v ∈ σ, Fintype.card (A v),
      x ≤ k ^ (w + 1) := by
    intro x hx
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hx
    calc ∏ v ∈ σ, Fintype.card (A v)
        ≤ k ^ σ.card := Finset.prod_le_pow_card σ _ k fun u _ => halpha u
      _ ≤ k ^ (w + 1) := Nat.pow_le_pow_right hk (hwidth σ hσ)
  calc (bags.map fun σ => ∏ v ∈ σ, Fintype.card (A v)).sum
      ≤ (bags.map fun σ => ∏ v ∈ σ, Fintype.card (A v)).length
          • k ^ (w + 1) := List.sum_le_card_nsmul _ _ hbound
    _ = bags.length * k ^ (w + 1) := by
        rw [List.length_map, nsmul_eq_mul, Nat.cast_id]

/-- **The realized total-space bound.**  Run an elimination order whose
steps materialize the (bag, constraint) pairs `steps`, every bag having
at most `w + 1` variables.  The total number of rows actually
materialized — the sum of the `encard`s of the per-step bag tables —
is at most `steps.length · k ^ (w + 1)`.  Combined with
`elimination_step`, an order of `n` buckets of width `w` decides the
problem materializing at most `n · k^{w+1}` rows in total. -/
theorem elimination_order_table_total_bound [∀ u, Fintype (A u)]
    (steps : List (Finset V × Set (∀ v, A v))) {k w : ℕ} (hk : 0 < k)
    (halpha : ∀ u : V, Fintype.card (A u) ≤ k)
    (hwidth : ∀ p ∈ steps, p.1.card ≤ w + 1) :
    (steps.map fun p => (table (↑p.1 : Set V) p.2).encard).sum
      ≤ (steps.length : ℕ∞) * ((k ^ (w + 1) : ℕ) : ℕ∞) := by
  have hbound : ∀ x ∈ steps.map fun p => (table (↑p.1 : Set V) p.2).encard,
      x ≤ ((k ^ (w + 1) : ℕ) : ℕ∞) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact table_encard_le_pow_finset p.1 p.2 hk halpha (hwidth p hp)
  calc (steps.map fun p => (table (↑p.1 : Set V) p.2).encard).sum
      ≤ (steps.map fun p => (table (↑p.1 : Set V) p.2).encard).length
          • ((k ^ (w + 1) : ℕ) : ℕ∞) := List.sum_le_card_nsmul _ _ hbound
    _ = (steps.length : ℕ∞) * ((k ^ (w + 1) : ℕ) : ℕ∞) := by
        rw [List.length_map, nsmul_eq_mul]

/-! ### Cut elimination dissolves joint feasibility -/

/-- **Disjoint scopes make joint feasibility independent.**  Two
constraints with disjoint supports are jointly satisfiable iff each is
satisfiable on its own: the splice of two separate witnesses along `σ`
is a joint witness.  Pi-space counterpart of the block product
`feasibilitySet_blockFamily`. -/
theorem inter_nonempty_iff_of_disjoint_support {T U : Set (∀ v, A v)}
    {σ τ : Set V} (hT : HasSupport T σ) (hU : HasSupport U τ)
    (hdisj : Disjoint σ τ) :
    (T ∩ U).Nonempty ↔ T.Nonempty ∧ U.Nonempty := by
  constructor
  · rintro ⟨f, hfT, hfU⟩
    exact ⟨⟨f, hfT⟩, ⟨f, hfU⟩⟩
  · classical
    rintro ⟨⟨f, hf⟩, ⟨g, hg⟩⟩
    refine ⟨σ.piecewise f g, ?_, ?_⟩
    · exact (hT f (σ.piecewise f g) fun u hu =>
        (Set.piecewise_eq_of_mem σ f g hu).symm).mp hf
    · refine (hU g (σ.piecewise f g) fun u hu => ?_).mp hg
      exact (Set.piecewise_eq_of_notMem σ f g
        (Set.disjoint_right.mp hdisj hu)).symm

/-- **Cut elimination, feasibility form.**  If `T` and `U` share only
the cut variable `v`, then after conditioning on `v` the joint problem
is satisfiable iff each conditioned constraint is satisfiable
separately: eliminating a cut variable turns joint feasibility into
independent per-block checks. -/
theorem condition_inter_nonempty_iff {T U : Set (∀ v, A v)}
    {σ τ : Set V} (v : V) (a : A v) (hT : HasSupport T σ)
    (hU : HasSupport U τ) (hcut : σ ∩ τ ⊆ {v}) :
    (condition (T ∩ U) v a).Nonempty
      ↔ (condition T v a).Nonempty ∧ (condition U v a).Nonempty := by
  rw [condition_inter]
  exact inter_nonempty_iff_of_disjoint_support (hT.condition v a)
    (hU.condition v a) (sdiff_disjoint_of_cut hcut)

end STE
