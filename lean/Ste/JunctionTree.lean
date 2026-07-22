/-
The junction-tree representation: polynomial-size bag tables.

`Ste.Elimination` runs bucket elimination and bounds the total table
space of a run (`bucketEliminate_total_space`); `Ste.Treedecomp`
attains the minimum elimination width (`inducedTreewidth`,
`bucketEliminate_treewidth_bound`).  This file packages the OUTPUT of
such a run as a data structure — the **junction-tree representation**:
the list of per-bag projected tables, one `table` per materialized
bucket — and proves it is a *faithful*, *polynomial-size*
representation of the instance at bounded treewidth.

Main results:

* `junctionTables` / `junctionSize`: the representation (the bag table
  `table ↑bag constraint` for each `(bag, constraint)` pair of
  `bucketBags order B`) and its total size, the sum of the per-bag
  table `encard`s.
* `junctionTree_size_le` — **the polynomial-size theorem**: for any
  instance `B` of scoped constraints over alphabets of size at most
  `k`, some complete elimination order decides feasibility, each
  materialized constraint is faithfully recovered from its bag table,
  and the total representation size is at most
  `n * k^(inducedTreewidth B + 1)` with `n` the number of elimination
  steps.  For FIXED width `w := inducedTreewidth B` this is polynomial
  — linear in `n` — even though the feasible set itself can be
  exponential in `n`.
* `junctionTree_size_linear` — **the fixed-width `O(n)` corollary**:
  for a duplicate-free complete order of width `w`, the size bound is
  `n * C` with `n := Fintype.card V` the number of variables and
  `C := k ^ (w + 1)` a constant independent of `n`.
  `junctionTree_size_le_card` attains it at the minimal
  duplicate-free width `junctionWidth B ≥ inducedTreewidth B`
  (`inducedTreewidth_le_junctionWidth`).
* **Faithfulness**: `HasSupport.mem_iff_restrict` — membership in a
  scoped constraint is exactly membership of the restricted assignment
  in the bag table; `mem_joinConstraint_iff_restrict` — a global
  assignment is feasible for the whole instance iff it restricts into
  EVERY bag table of `B`: the family of bag tables represents the
  feasible set exactly, losing no information.
  `junctionTables_faithful` — every constraint the run materializes is
  the preimage of its bag table.  The elimination fold's decision
  (`bucketEliminate_decides`, packaged into `junctionTree_size_le`)
  certifies feasibility from these tables.

What stays outlook (NOT mechanized here): the lower-bound side — that
un-bounded-width instances *escape* every such small representation.
The witness shape is already in the library: the fully coupled
`diagonal` is not rectangular (`diagonal_not_rectangular`, in
`Ste.Sheaf`) and needs its full scope (`diagonal_support_full`, in
`Ste.Support`), so no per-variable (width-0) table family represents
it; scaling this to a quantitative `2^n` lower bound against width-`w`
representations is future work.  Also outlook: that the minimal
duplicate-free width `junctionWidth` coincides with `inducedTreewidth`
(repeated eliminations only ever add empty bags, but the simulation
argument is not mechanized).

Reference: R. Dechter, *Constraint Processing*, 2003 (bucket
elimination, induced width, junction / join trees);
N. Robertson, P. D. Seymour, *Graph minors II: algorithmic aspects of
tree-width*, 1986.
-/
import Ste.Treedecomp
import Mathlib.Data.Fintype.Card

namespace STE

open Set

variable {V : Type*} {A : V → Type*} [DecidableEq V]

/-! ### Faithfulness of a single bag table -/

/-- Restriction lands in the table: the projection to any scope `σ` of
a member of `T` is a row of the `σ`-table of `T`. -/
theorem restrict_mem_table (σ : Set V) {T : Set (∀ v, A v)}
    {f : ∀ v, A v} (hf : f ∈ T) :
    (fun v : σ => f v) ∈ table σ T :=
  Set.mem_image_of_mem _ hf

/-- **Membership is table membership.**  For a constraint supported on
`σ`, a global assignment satisfies the constraint iff its restriction
to `σ` is a row of the bag table: the table carries exactly the
information of the constraint.  Pointwise form of
`HasSupport.eq_preimage_table`. -/
theorem HasSupport.mem_iff_restrict {T : Set (∀ v, A v)} {σ : Set V}
    (hT : HasSupport T σ) (f : ∀ v, A v) :
    f ∈ T ↔ (fun v : σ => f v) ∈ table σ T := by
  constructor
  · exact fun hf => Set.mem_image_of_mem _ hf
  · rintro ⟨g, hg, hgf⟩
    exact (hT g f fun v hv => congrFun hgf ⟨v, hv⟩).mp hg

/-- **The bag tables represent the instance.**  A global assignment is
feasible for the whole instance `B` — it satisfies the joint
constraint — iff it restricts into EVERY bag table: the family of
per-bag tables is a faithful representation of the feasible set, not
just a size certificate. -/
theorem mem_joinConstraint_iff_restrict
    {B : List (Finset V × Set (∀ v, A v))}
    (hsupp : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V)) (f : ∀ v, A v) :
    f ∈ joinConstraint B
      ↔ ∀ q ∈ B,
          (fun v : (↑q.1 : Set V) => f v) ∈ table (↑q.1 : Set V) q.2 := by
  rw [mem_joinConstraint]
  exact forall₂_congr fun q hq => (hsupp q hq).mem_iff_restrict f

/-! ### The junction-tree representation and its size -/

/-- The **junction-tree representation** of the run of an elimination
order on the instance `B`: for each `(bag, constraint)` pair the run
materializes (`bucketBags`), the projected bag table
`table ↑bag constraint`.  This is the per-bag table family of bucket
elimination / junction-tree algorithms (Dechter 2003). -/
def junctionTables (order : List ((v : V) × A v))
    (B : List (Finset V × Set (∀ v, A v))) :
    List ((σ : Finset V) × Set (∀ v : (↑σ : Set V), A (v : V))) :=
  (bucketBags order B).map fun q => ⟨q.1, table (↑q.1 : Set V) q.2⟩

/-- The **total size** of the junction-tree representation: the sum of
the `encard`s of the per-bag tables — the total number of rows
materialized. -/
noncomputable def junctionSize (order : List ((v : V) × A v))
    (B : List (Finset V × Set (∀ v, A v))) : ℕ∞ :=
  ((junctionTables order B).map fun t => t.2.encard).sum

/-- The representation size is the quantity
`bucketEliminate_total_space` bounds: the sum of the bag-table
`encard`s over the trace of the run. -/
theorem junctionSize_eq (order : List ((v : V) × A v))
    (B : List (Finset V × Set (∀ v, A v))) :
    junctionSize order B
      = ((bucketBags order B).map
          fun q => (table (↑q.1 : Set V) q.2).encard).sum := by
  unfold junctionSize junctionTables
  simp [List.map_map, Function.comp_def]

/-- A run of `n` elimination steps produces a representation of `n`
tables. -/
theorem length_junctionTables (order : List ((v : V) × A v))
    (B : List (Finset V × Set (∀ v, A v))) :
    (junctionTables order B).length = order.length := by
  rw [junctionTables, List.length_map, length_bucketBags]

/-- **Every materialized constraint is its bag table.**  Along the run,
each `(bag, constraint)` pair satisfies: the constraint is exactly the
preimage of its bag table — the junction-tree representation loses no
information about any intermediate constraint. -/
theorem junctionTables_faithful (order : List ((v : V) × A v))
    {B : List (Finset V × Set (∀ v, A v))}
    (hsupp : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V)) :
    ∀ q ∈ bucketBags order B,
      q.2 = (fun f (v : (↑q.1 : Set V)) => f v) ⁻¹'
        table (↑q.1 : Set V) q.2 :=
  fun q hq => (bucketBags_support order hsupp q hq).eq_preimage_table

/-- Pointwise form of `junctionTables_faithful`: an assignment
satisfies a materialized constraint iff its restriction is a row of
the corresponding bag table. -/
theorem mem_bucketBags_iff_restrict (order : List ((v : V) × A v))
    {B : List (Finset V × Set (∀ v, A v))}
    (hsupp : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V)) :
    ∀ q ∈ bucketBags order B, ∀ f : ∀ v, A v,
      f ∈ q.2
        ↔ (fun v : (↑q.1 : Set V) => f v) ∈ table (↑q.1 : Set V) q.2 :=
  fun q hq f => (bucketBags_support order hsupp q hq).mem_iff_restrict f

/-! ### The size bounds -/

/-- **Width-`w` orders give `n · k^(w+1)` representations.**  If every
bag the run materializes has at most `w + 1` variables, then over
alphabets of size at most `k` the junction-tree representation has
total size at most `order.length * k ^ (w + 1)`.  Wrapper of
`bucketEliminate_total_space` in terms of `junctionSize`. -/
theorem junctionSize_le_width [∀ u, Fintype (A u)]
    (order : List ((v : V) × A v))
    (B : List (Finset V × Set (∀ v, A v))) {k w : ℕ} (hk : 0 < k)
    (halpha : ∀ u : V, Fintype.card (A u) ≤ k)
    (hwidth : ∀ q ∈ bucketBags order B, q.1.card ≤ w + 1) :
    junctionSize order B
      ≤ (order.length : ℕ∞) * ((k ^ (w + 1) : ℕ) : ℕ∞) := by
  rw [junctionSize_eq]
  exact bucketEliminate_total_space order B hk halpha hwidth

/-- **The polynomial-size junction-tree theorem.**  For any instance
`B` of scoped constraints over a finite variable set with inhabited
alphabets of size at most `k`, there EXISTS a complete elimination
order such that

1. *(completeness)* the order covers every scope of `B`;
2. *(decision)* the elimination residue of the joint constraint is
   `Set.univ` or `∅` — the run decides feasibility
   (`bucketEliminate_decides`);
3. *(faithfulness)* every constraint the run materializes is exactly
   the preimage of its bag table — the representation carries the run;
4. *(size)* the total representation size is at most
   `n * k ^ (inducedTreewidth B + 1)`, where `n = order.length` is the
   number of elimination steps (= number of tables,
   `length_junctionTables`).

For FIXED width `w := inducedTreewidth B` the bound is polynomial —
linear in the number of elimination steps — although the feasible set
itself can have size exponential in the number of variables: the
exponential is confined to the bag width.  (Dechter 2003;
Robertson–Seymour.) -/
theorem junctionTree_size_le [Fintype V] [∀ v, Nonempty (A v)]
    [∀ u, Fintype (A u)]
    (B : List (Finset V × Set (∀ v, A v))) {k : ℕ} (hk : 0 < k)
    (halpha : ∀ u : V, Fintype.card (A u) ≤ k)
    (hsupp : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V)) :
    ∃ order : List ((v : V) × A v),
      (∀ q ∈ B, (↑q.1 : Set V) ⊆ eliminated order)
        ∧ (eliminate order (joinConstraint B) = Set.univ
            ∨ eliminate order (joinConstraint B) = ∅)
        ∧ (∀ q ∈ bucketBags order B,
            q.2 = (fun f (v : (↑q.1 : Set V)) => f v) ⁻¹'
              table (↑q.1 : Set V) q.2)
        ∧ junctionSize order B
            ≤ (order.length : ℕ∞)
                * ((k ^ (inducedTreewidth B + 1) : ℕ) : ℕ∞) := by
  obtain ⟨order, hcover, hwidth⟩ := achievesWidth_inducedTreewidth B
  exact ⟨order, hcover, (bucketEliminate_decides order hsupp hcover).2,
    junctionTables_faithful order hsupp,
    junctionSize_le_width order B hk halpha hwidth⟩

/-! ### The fixed-width `O(n)` corollary

To read `n` as the number of VARIABLES (not elimination steps) we use
duplicate-free orders: an order that eliminates each variable at most
once has length at most `Fintype.card V`. -/

/-- **Fixed width is linear size.**  Let `order` be a duplicate-free
elimination order (no variable eliminated twice) of width `w` on `B`,
over alphabets of size at most `k`.  Then with `n := Fintype.card V`
the number of variables and `C := k ^ (w + 1)` — a constant depending
only on the alphabet bound `k` and the width `w`, NOT on `n` — the
junction-tree representation has total size at most `n * C`: at fixed
width the representation is `O(n)`. -/
theorem junctionTree_size_linear [Fintype V] [∀ u, Fintype (A u)]
    (order : List ((v : V) × A v))
    (B : List (Finset V × Set (∀ v, A v))) {k w C : ℕ} (hk : 0 < k)
    (hC : C = k ^ (w + 1))
    (halpha : ∀ u : V, Fintype.card (A u) ≤ k)
    (hnodup : (order.map Sigma.fst).Nodup)
    (hwidth : ∀ q ∈ bucketBags order B, q.1.card ≤ w + 1) :
    junctionSize order B
      ≤ ((Fintype.card V : ℕ) : ℕ∞) * ((C : ℕ) : ℕ∞) := by
  subst hC
  have hlen : order.length ≤ Fintype.card V := by
    simpa using hnodup.length_le_card
  calc junctionSize order B
      ≤ (order.length : ℕ∞) * ((k ^ (w + 1) : ℕ) : ℕ∞) :=
        junctionSize_le_width order B hk halpha hwidth
    _ ≤ ((Fintype.card V : ℕ) : ℕ∞) * ((k ^ (w + 1) : ℕ) : ℕ∞) :=
        mul_le_mul_right' (ENat.coe_le_coe.mpr hlen) _

/-! ### The attained duplicate-free width -/

/-- **Duplicate-free achievable width.**  Some elimination order that
eliminates each variable at most once is complete for `B` and
materializes only bags of at most `w + 1` variables.  Strengthening of
`AchievesWidth` by the `Nodup` condition that makes the order length —
hence the representation size — linear in the number of variables. -/
def AchievesWidthNodup (B : List (Finset V × Set (∀ v, A v)))
    (w : ℕ) : Prop :=
  ∃ order : List ((v : V) × A v),
    (order.map Sigma.fst).Nodup
      ∧ (∀ q ∈ B, (↑q.1 : Set V) ⊆ eliminated order)
      ∧ ∀ q ∈ bucketBags order B, q.1.card ≤ w + 1

/-- The trivial all-variables order eliminates each variable exactly
once. -/
theorem elimAll_nodup [Fintype V] [∀ v, Nonempty (A v)] :
    ((elimAll V A).map Sigma.fst).Nodup := by
  unfold elimAll
  rw [List.map_map]
  exact Finset.univ.nodup_toList.map fun _ _ h => h

/-- The duplicate-free width predicate is satisfiable: the trivial
all-variables order witnesses width `Fintype.card V`. -/
theorem achievesWidthNodup_card [Fintype V] [∀ v, Nonempty (A v)]
    (B : List (Finset V × Set (∀ v, A v))) :
    AchievesWidthNodup B (Fintype.card V) := by
  refine ⟨elimAll V A, elimAll_nodup, ?_, ?_⟩
  · intro q _
    rw [eliminated_elimAll]
    exact Set.subset_univ _
  · intro q _
    exact le_trans (Finset.card_le_univ q.1) (Nat.le_succ _)

/-- The **junction width** of the instance: the least width achieved by
a duplicate-free complete elimination order.  At most `Fintype.card V`,
at least `inducedTreewidth B`
(`inducedTreewidth_le_junctionWidth`). -/
noncomputable def junctionWidth
    (B : List (Finset V × Set (∀ v, A v))) : ℕ :=
  sInf {w | AchievesWidthNodup B w}

/-- The minimal duplicate-free width is attained by a concrete
order. -/
theorem achievesWidthNodup_junctionWidth [Fintype V]
    [∀ v, Nonempty (A v)] (B : List (Finset V × Set (∀ v, A v))) :
    AchievesWidthNodup B (junctionWidth B) :=
  Nat.sInf_mem ⟨Fintype.card V, achievesWidthNodup_card B⟩

/-- Duplicate-free orders are in particular orders: the induced
treewidth is at most the junction width.  (That the two coincide —
repeated eliminations only add empty bags — is not mechanized;
outlook.) -/
theorem inducedTreewidth_le_junctionWidth [Fintype V]
    [∀ v, Nonempty (A v)] (B : List (Finset V × Set (∀ v, A v))) :
    inducedTreewidth B ≤ junctionWidth B := by
  obtain ⟨order, _, hcover, hwidth⟩ := achievesWidthNodup_junctionWidth B
  exact inducedTreewidth_le ⟨order, hcover, hwidth⟩

/-- **The `O(n)` junction-tree theorem, existence form.**  For any
instance `B` of scoped constraints over a finite variable set with
inhabited alphabets of size at most `k`, some complete elimination
order decides feasibility AND yields a junction-tree representation of
total size at most `n * k ^ (junctionWidth B + 1)`, where
`n := Fintype.card V` is the number of variables.  With `k` and the
width fixed, the representation of the (possibly exponentially large)
feasible set is linear in the number of variables. -/
theorem junctionTree_size_le_card [Fintype V] [∀ v, Nonempty (A v)]
    [∀ u, Fintype (A u)]
    (B : List (Finset V × Set (∀ v, A v))) {k : ℕ} (hk : 0 < k)
    (halpha : ∀ u : V, Fintype.card (A u) ≤ k)
    (hsupp : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V)) :
    ∃ order : List ((v : V) × A v),
      (∀ q ∈ B, (↑q.1 : Set V) ⊆ eliminated order)
        ∧ (eliminate order (joinConstraint B) = Set.univ
            ∨ eliminate order (joinConstraint B) = ∅)
        ∧ junctionSize order B
            ≤ ((Fintype.card V : ℕ) : ℕ∞)
                * ((k ^ (junctionWidth B + 1) : ℕ) : ℕ∞) := by
  obtain ⟨order, hnodup, hcover, hwidth⟩ :=
    achievesWidthNodup_junctionWidth B
  exact ⟨order, hcover, (bucketEliminate_decides order hsupp hcover).2,
    junctionTree_size_linear order B hk rfl halpha hnodup hwidth⟩

/-! ### Contrast: full coupling escapes small scopes

The bounds above confine the exponential to the bag width; they say
nothing when the width is unbounded, and the library already exhibits
the obstruction shape.  The fully coupled `diagonal` constraint
`{f | f 0 = f 1}` is not rectangular (`diagonal_not_rectangular`,
`Ste.Sheaf`): no family of per-variable — i.e. width-0 bag — tables
represents it.  And its scope cannot be shrunk at all
(`diagonal_support_full`, `Ste.Support`): every support contains both
variables, so any faithful bag must contain the full coupled scope.
Scaling this to a quantitative lower bound (an `n`-variable coupled
instance whose every width-`w` table family has size `≥ 2^Ω(n)`) is
the un-mechanized lower-bound side of the treewidth story; outlook. -/

end STE
