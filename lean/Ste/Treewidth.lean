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
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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
