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

end STE
