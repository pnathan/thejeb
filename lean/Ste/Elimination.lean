/-
The elimination fold: running a whole elimination order.

`Ste.Treewidth` bounds a single elimination step (`elimination_step`)
and the total table space of an order (`elimination_order_total_bound`).
This file mechanizes *running* an order: fold conditioning over a list
of `(variable, value)` elimination steps.

Main results:

* `HasSupport.eliminate`: after running an order, the support of the
  constraint is the original support minus the eliminated variables —
  scope accounting for the whole run.
* `mem_eliminate_iff`: elimination is substitution — membership in the
  fully eliminated constraint is membership of the substituted
  assignment in the original one.
* `eliminate_eq_univ_or_empty`: a **complete** order (one whose
  eliminated variables cover a support) decides the constraint: the
  final residue is `univ` or `∅`.
* `condition_eq_self`: conditioning on a variable outside the scope
  does nothing — the algebraic fact that lets bucket elimination touch
  only the bucket of the current variable.

Reference: R. Dechter, *Constraint Processing*, 2003.
-/
import Ste.Treewidth

namespace STE

open Set

variable {V : Type*} {A : V → Type*} [DecidableEq V]

/-! ### Conditioning outside the scope is trivial -/

/-- **Conditioning outside the scope does nothing.**  Fixing a variable
that a constraint does not depend on leaves the constraint unchanged:
bucket elimination may ignore the constraints outside the current
bucket. -/
theorem condition_eq_self {T : Set (∀ v, A v)} {σ : Set V}
    (hT : HasSupport T σ) {v : V} (hv : v ∉ σ) (a : A v) :
    condition T v a = T := by
  ext f
  rw [mem_condition_iff]
  refine hT _ _ fun u hu => ?_
  have huv : u ≠ v := fun h => hv (h ▸ hu)
  exact Function.update_of_ne huv a f

/-! ### The elimination fold -/

/-- Run an elimination order: fold conditioning over a list of
`(variable, value)` elimination steps. -/
def eliminate (order : List ((v : V) × A v)) (T : Set (∀ v, A v)) :
    Set (∀ v, A v) :=
  order.foldl (fun S p => condition S p.1 p.2) T

@[simp] theorem eliminate_nil (T : Set (∀ v, A v)) :
    eliminate [] T = T := rfl

theorem eliminate_cons (p : (v : V) × A v) (order : List ((v : V) × A v))
    (T : Set (∀ v, A v)) :
    eliminate (p :: order) T = eliminate order (condition T p.1 p.2) := rfl

/-- The set of variables an order eliminates. -/
def eliminated (order : List ((v : V) × A v)) : Set V :=
  {u | u ∈ order.map Sigma.fst}

@[simp] theorem eliminated_nil :
    eliminated ([] : List ((v : V) × A v)) = ∅ := by
  ext u
  simp [eliminated]

theorem eliminated_cons (p : (v : V) × A v)
    (order : List ((v : V) × A v)) :
    eliminated (p :: order) = {p.1} ∪ eliminated order := by
  ext u
  simp [eliminated, List.mem_cons]

/-- **Scope accounting for a whole run.**  Running an elimination order
removes every eliminated variable from the support: the residual
constraint lives on `σ \ eliminated order`. -/
theorem HasSupport.eliminate {T : Set (∀ v, A v)} {σ : Set V}
    (hT : HasSupport T σ) (order : List ((v : V) × A v)) :
    HasSupport (STE.eliminate order T) (σ \ eliminated order) := by
  induction order generalizing T σ with
  | nil => simpa using hT
  | cons p order ih =>
      rw [eliminate_cons, eliminated_cons]
      have h := ih (hT.condition p.1 p.2)
      rwa [Set.sdiff_sdiff] at h

/-- **Elimination is substitution.**  An assignment survives the full
elimination fold iff overwriting it with all the eliminated values
satisfies the original constraint. -/
theorem mem_eliminate_iff {T : Set (∀ v, A v)}
    (order : List ((v : V) × A v)) (f : ∀ v, A v) :
    f ∈ eliminate order T
      ↔ order.foldr (fun p g => Function.update g p.1 p.2) f ∈ T := by
  induction order generalizing T with
  | nil => rfl
  | cons p order ih =>
      rw [eliminate_cons, ih, mem_condition_iff]
      rfl

/-- **A complete elimination order decides the constraint.**  If the
order eliminates every variable of a support of `T`, the fully
eliminated constraint is trivial: `univ` (every completion of the
eliminated values succeeds) or `∅` (none does).  Running the order to
the end leaves a decision, not a constraint. -/
theorem eliminate_eq_univ_or_empty {T : Set (∀ v, A v)} {σ : Set V}
    (hT : HasSupport T σ) {order : List ((v : V) × A v)}
    (hcover : σ ⊆ eliminated order) :
    eliminate order T = Set.univ ∨ eliminate order T = ∅ := by
  have h := hT.eliminate order
  rw [Set.sdiff_eq_empty.mpr hcover] at h
  exact (hasSupport_empty_iff _).mp h

/-! ### Bucket elimination: the full data-structure fold

The state of bucket elimination is a list of constraints with `Finset`
scopes.  One step at `(v, a)` collects the bucket of constraints whose
scope contains `v`, joins them, conditions on `v`, and returns the
joined constraint on the bucket bag minus `v` together with the
untouched rest. -/

/-- The union of the scopes of a constraint list. -/
def joinScope (L : List (Finset V × Set (∀ v, A v))) : Finset V :=
  L.foldr (fun q σ => q.1 ∪ σ) ∅

@[simp] theorem joinScope_nil :
    joinScope ([] : List (Finset V × Set (∀ v, A v))) = ∅ := rfl

@[simp] theorem joinScope_cons (q : Finset V × Set (∀ v, A v))
    (L : List (Finset V × Set (∀ v, A v))) :
    joinScope (q :: L) = q.1 ∪ joinScope L := rfl

/-- The join (conjunction) of a constraint list. -/
def joinConstraint (L : List (Finset V × Set (∀ v, A v))) :
    Set (∀ v, A v) :=
  L.foldr (fun q S => q.2 ∩ S) Set.univ

@[simp] theorem joinConstraint_nil :
    joinConstraint ([] : List (Finset V × Set (∀ v, A v))) = Set.univ :=
  rfl

@[simp] theorem joinConstraint_cons (q : Finset V × Set (∀ v, A v))
    (L : List (Finset V × Set (∀ v, A v))) :
    joinConstraint (q :: L) = q.2 ∩ joinConstraint L := rfl

theorem mem_joinScope {L : List (Finset V × Set (∀ v, A v))} {u : V} :
    u ∈ joinScope L ↔ ∃ q ∈ L, u ∈ q.1 := by
  induction L with
  | nil => simp
  | cons q L ih =>
      rw [joinScope_cons, Finset.mem_union, ih]
      constructor
      · rintro (hu | ⟨r, hr, hru⟩)
        · exact ⟨q, List.mem_cons.mpr (Or.inl rfl), hu⟩
        · exact ⟨r, List.mem_cons_of_mem q hr, hru⟩
      · rintro ⟨r, hr, hru⟩
        rcases List.mem_cons.mp hr with rfl | hr
        · exact Or.inl hru
        · exact Or.inr ⟨r, hr, hru⟩

theorem mem_joinConstraint {L : List (Finset V × Set (∀ v, A v))}
    {f : ∀ v, A v} :
    f ∈ joinConstraint L ↔ ∀ q ∈ L, f ∈ q.2 := by
  induction L with
  | nil => simp
  | cons q L ih =>
      rw [joinConstraint_cons, List.forall_mem_cons, ← ih]
      exact Set.mem_inter_iff f q.2 (joinConstraint L)

/-- **The join is supported on the union of the scopes** — the list
form of `HasSupport.iInter`. -/
theorem hasSupport_joinConstraint (L : List (Finset V × Set (∀ v, A v)))
    (h : ∀ q ∈ L, HasSupport q.2 (↑q.1 : Set V)) :
    HasSupport (joinConstraint L) (↑(joinScope L) : Set V) := by
  induction L with
  | nil => simpa using hasSupport_empty_of_univ
  | cons q L ih =>
      rw [joinConstraint_cons, joinScope_cons, Finset.coe_union]
      exact (h q (List.mem_cons.mpr (Or.inl rfl))).inter_union
        (ih fun r hr => h r (List.mem_cons_of_mem q hr))

/-- Every scope in the list is contained in `C` iff the joined scope
is. -/
theorem coe_joinScope_subset {L : List (Finset V × Set (∀ v, A v))}
    {C : Set V} (h : ∀ q ∈ L, (↑q.1 : Set V) ⊆ C) :
    (↑(joinScope L) : Set V) ⊆ C := by
  intro u hu
  obtain ⟨q, hq, hqu⟩ := mem_joinScope.mp (Finset.mem_coe.mp hu)
  exact h q hq (Finset.mem_coe.mpr hqu)

/-- The constraint one bucket step materializes: the bucket of `v` —
the constraints whose scope contains `v` — joined and conditioned on
`v := a`, scoped on the bucket bag minus `v`. -/
def bucketHead (p : (v : V) × A v)
    (B : List (Finset V × Set (∀ v, A v))) :
    Finset V × Set (∀ v, A v) :=
  ((joinScope (B.filter fun q => p.1 ∈ q.1)).erase p.1,
    condition (joinConstraint (B.filter fun q => p.1 ∈ q.1)) p.1 p.2)

@[simp] theorem bucketHead_fst (p : (v : V) × A v)
    (B : List (Finset V × Set (∀ v, A v))) :
    (bucketHead p B).1
      = (joinScope (B.filter fun q => p.1 ∈ q.1)).erase p.1 := rfl

@[simp] theorem bucketHead_snd (p : (v : V) × A v)
    (B : List (Finset V × Set (∀ v, A v))) :
    (bucketHead p B).2
      = condition (joinConstraint (B.filter fun q => p.1 ∈ q.1))
          p.1 p.2 := rfl

/-- **One step of bucket elimination** at `(v, a)`: replace the bucket
of `v` by its joined, conditioned residue and keep the rest. -/
def bucketStep (p : (v : V) × A v)
    (B : List (Finset V × Set (∀ v, A v))) :
    List (Finset V × Set (∀ v, A v)) :=
  bucketHead p B :: B.filter fun q => p.1 ∉ q.1

theorem bucketStep_eq (p : (v : V) × A v)
    (B : List (Finset V × Set (∀ v, A v))) :
    bucketStep p B
      = bucketHead p B :: B.filter fun q => p.1 ∉ q.1 := rfl

/-- The materialized bucket constraint is supported on its bag. -/
theorem bucketHead_support (p : (v : V) × A v)
    {B : List (Finset V × Set (∀ v, A v))}
    (h : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V)) :
    HasSupport (bucketHead p B).2 (↑(bucketHead p B).1 : Set V) := by
  rw [bucketHead_fst, bucketHead_snd, Finset.coe_erase]
  exact (hasSupport_joinConstraint _
    fun q hq => h q (List.mem_of_mem_filter hq)).condition p.1 p.2

/-- **Invariant: scopes.**  A bucket step preserves the invariant that
every constraint is supported on its recorded scope. -/
theorem bucketStep_support (p : (v : V) × A v)
    {B : List (Finset V × Set (∀ v, A v))}
    (h : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V)) :
    ∀ q ∈ bucketStep p B, HasSupport q.2 (↑q.1 : Set V) := by
  intro q hq
  rw [bucketStep_eq] at hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact bucketHead_support p h
  · exact h q (List.mem_of_mem_filter hq)

/-- **Invariant: elimination.**  After the step at `v`, no live scope
contains `v` (and scopes only shrink). -/
theorem bucketStep_scope_subset (p : (v : V) × A v)
    {B : List (Finset V × Set (∀ v, A v))} {C : Set V}
    (h : ∀ q ∈ B, (↑q.1 : Set V) ⊆ C) :
    ∀ q ∈ bucketStep p B, (↑q.1 : Set V) ⊆ C \ {p.1} := by
  intro q hq
  rw [bucketStep_eq] at hq
  rcases List.mem_cons.mp hq with rfl | hq
  · rw [bucketHead_fst, Finset.coe_erase]
    exact Set.sdiff_subset_sdiff_left (coe_joinScope_subset
      fun r hr => h r (List.mem_of_mem_filter hr))
  · have hqB : q ∈ B := List.mem_of_mem_filter hq
    have hnp : p.1 ∉ q.1 := of_decide_eq_true (List.mem_filter.mp hq).2
    intro u hu
    refine ⟨h q hqB hu, fun he => hnp ?_⟩
    have hue : u = p.1 := Set.mem_singleton_iff.mp he
    exact hue ▸ Finset.mem_coe.mp hu

/-- **The step is conditioning of the joint constraint.**  Joining the
whole state after a bucket step is exactly conditioning the joint
constraint of the previous state: the data structure faithfully tracks
the problem.  The rest of the constraints need no update because
conditioning outside their scope is trivial. -/
theorem joinConstraint_bucketStep (p : (v : V) × A v)
    {B : List (Finset V × Set (∀ v, A v))}
    (h : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V)) :
    joinConstraint (bucketStep p B)
      = condition (joinConstraint B) p.1 p.2 := by
  ext f
  rw [bucketStep_eq, mem_joinConstraint, mem_condition_iff,
    mem_joinConstraint]
  constructor
  · intro hf q hqB
    by_cases hv : p.1 ∈ q.1
    · have hhead : f ∈ (bucketHead p B).2 :=
        hf (bucketHead p B) (List.mem_cons.mpr (Or.inl rfl))
      rw [bucketHead_snd, mem_condition_iff, mem_joinConstraint]
        at hhead
      exact hhead q (List.mem_filter.mpr ⟨hqB, decide_eq_true hv⟩)
    · have hq : q ∈ B.filter fun q => p.1 ∉ q.1 :=
        List.mem_filter.mpr ⟨hqB, decide_eq_true hv⟩
      have hfq : f ∈ q.2 := hf q (List.mem_cons_of_mem _ hq)
      exact (h q hqB f (Function.update f p.1 p.2) fun u hu =>
        (Function.update_of_ne (fun e : u = p.1 =>
          hv (e ▸ Finset.mem_coe.mp hu)) p.2 f).symm).mp hfq
  · intro hall q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [bucketHead_snd, mem_condition_iff, mem_joinConstraint]
      exact fun r hr => hall r (List.mem_of_mem_filter hr)
    · have hqB : q ∈ B := List.mem_of_mem_filter hq
      have hnp : p.1 ∉ q.1 := of_decide_eq_true (List.mem_filter.mp hq).2
      exact (h q hqB f (Function.update f p.1 p.2) fun u hu =>
        (Function.update_of_ne (fun e : u = p.1 =>
          hnp (e ▸ Finset.mem_coe.mp hu)) p.2 f).symm).mpr (hall q hqB)

/-- Run bucket elimination along a whole order. -/
def bucketEliminate (order : List ((v : V) × A v))
    (B : List (Finset V × Set (∀ v, A v))) :
    List (Finset V × Set (∀ v, A v)) :=
  order.foldl (fun B p => bucketStep p B) B

@[simp] theorem bucketEliminate_nil
    (B : List (Finset V × Set (∀ v, A v))) :
    bucketEliminate [] B = B := rfl

theorem bucketEliminate_cons (p : (v : V) × A v)
    (order : List ((v : V) × A v))
    (B : List (Finset V × Set (∀ v, A v))) :
    bucketEliminate (p :: order) B
      = bucketEliminate order (bucketStep p B) := rfl

/-- The support invariant holds along the whole run. -/
theorem bucketEliminate_support (order : List ((v : V) × A v))
    {B : List (Finset V × Set (∀ v, A v))}
    (h : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V)) :
    ∀ q ∈ bucketEliminate order B, HasSupport q.2 (↑q.1 : Set V) := by
  induction order generalizing B with
  | nil => exact h
  | cons p order ih => exact ih (bucketStep_support p h)

/-- **The fold computes the elimination of the joint constraint.**
Bucket elimination is correct: the joint constraint of the final state
is the full elimination fold applied to the joint constraint of the
initial state. -/
theorem joinConstraint_bucketEliminate (order : List ((v : V) × A v))
    {B : List (Finset V × Set (∀ v, A v))}
    (h : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V)) :
    joinConstraint (bucketEliminate order B)
      = eliminate order (joinConstraint B) := by
  induction order generalizing B with
  | nil => rfl
  | cons p order ih =>
      rw [bucketEliminate_cons, eliminate_cons,
        ih (bucketStep_support p h), joinConstraint_bucketStep p h]

/-- **Scopes stay inside the not-yet-eliminated variables.**  After
running an order, every live scope avoids all eliminated variables. -/
theorem bucketEliminate_scope_subset (order : List ((v : V) × A v))
    {B : List (Finset V × Set (∀ v, A v))} {C : Set V}
    (h : ∀ q ∈ B, (↑q.1 : Set V) ⊆ C) :
    ∀ q ∈ bucketEliminate order B,
      (↑q.1 : Set V) ⊆ C \ eliminated order := by
  induction order generalizing B C with
  | nil =>
      intro q hq
      simpa using h q hq
  | cons p order ih =>
      intro q hq
      have h1 := ih (bucketStep_scope_subset p h) q hq
      rw [eliminated_cons]
      rwa [Set.sdiff_sdiff] at h1

/-- **Bucket elimination decides the problem.**  Run a complete
elimination order — one covering every initial scope — on a bucket
list.  Every surviving constraint has empty scope, hence is `univ` or
`∅`; and the joint constraint of the final state, which equals the
full elimination of the original joint constraint, is itself decided:
`univ` or `∅`. -/
theorem bucketEliminate_decides (order : List ((v : V) × A v))
    {B : List (Finset V × Set (∀ v, A v))}
    (hsupp : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V))
    (hcover : ∀ q ∈ B, (↑q.1 : Set V) ⊆ eliminated order) :
    (∀ q ∈ bucketEliminate order B, q.2 = Set.univ ∨ q.2 = ∅)
      ∧ (eliminate order (joinConstraint B) = Set.univ
          ∨ eliminate order (joinConstraint B) = ∅) := by
  have hempty : ∀ q ∈ bucketEliminate order B, (↑q.1 : Set V) = ∅ := by
    intro q hq
    have hs := bucketEliminate_scope_subset order hcover q hq
    rwa [Set.sdiff_self, Set.subset_empty_iff] at hs
  constructor
  · intro q hq
    have hs := bucketEliminate_support order hsupp q hq
    rw [hempty q hq] at hs
    exact (hasSupport_empty_iff _).mp hs
  · rw [← joinConstraint_bucketEliminate order hsupp]
    have hs := hasSupport_joinConstraint _
      (bucketEliminate_support order hsupp)
    have hjs : (↑(joinScope (bucketEliminate order B)) : Set V) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro u hu
      obtain ⟨q, hq, hqu⟩ := mem_joinScope.mp (Finset.mem_coe.mp hu)
      have h0 := hempty q hq
      rw [Set.eq_empty_iff_forall_notMem] at h0
      exact h0 u (Finset.mem_coe.mpr hqu)
    rw [hjs] at hs
    exact (hasSupport_empty_iff _).mp hs

/-! ### The trace of the run and its total space -/

/-- The trace of a bucket-elimination run: the (bag, constraint) pair
materialized at each step. -/
def bucketBags : List ((v : V) × A v)
    → List (Finset V × Set (∀ v, A v))
    → List (Finset V × Set (∀ v, A v))
  | [], _ => []
  | p :: order, B => bucketHead p B :: bucketBags order (bucketStep p B)

@[simp] theorem bucketBags_nil (B : List (Finset V × Set (∀ v, A v))) :
    bucketBags [] B = [] := rfl

theorem bucketBags_cons (p : (v : V) × A v)
    (order : List ((v : V) × A v))
    (B : List (Finset V × Set (∀ v, A v))) :
    bucketBags (p :: order) B
      = bucketHead p B :: bucketBags order (bucketStep p B) := rfl

/-- A run of `n` steps materializes `n` tables. -/
theorem length_bucketBags (order : List ((v : V) × A v))
    (B : List (Finset V × Set (∀ v, A v))) :
    (bucketBags order B).length = order.length := by
  induction order generalizing B with
  | nil => rfl
  | cons p order ih => simp [bucketBags_cons, ih]

/-- Every materialized constraint is supported on its bag — so by
`HasSupport.eq_preimage_table` each is *faithfully* represented by its
bag table. -/
theorem bucketBags_support (order : List ((v : V) × A v))
    {B : List (Finset V × Set (∀ v, A v))}
    (h : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V)) :
    ∀ q ∈ bucketBags order B, HasSupport q.2 (↑q.1 : Set V) := by
  induction order generalizing B with
  | nil =>
      intro q hq
      simp at hq
  | cons p order ih =>
      intro q hq
      rw [bucketBags_cons] at hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact bucketHead_support p h
      · exact ih (bucketStep_support p h) q hq

/-- **Total space of a bucket-elimination run.**  If every bag the run
materializes has at most `w + 1` variables — the order has width `w`
on this instance — then over alphabets of size at most `k` the total
size of all materialized tables is at most `n · k^{w+1}`, where `n` is
the number of elimination steps.  Together with
`bucketEliminate_decides`, a width-`w` elimination order decides
feasibility in `n · a^{w+1}` total table space. -/
theorem bucketEliminate_total_space [∀ u, Fintype (A u)]
    (order : List ((v : V) × A v))
    (B : List (Finset V × Set (∀ v, A v))) {k w : ℕ} (hk : 0 < k)
    (halpha : ∀ u : V, Fintype.card (A u) ≤ k)
    (hwidth : ∀ q ∈ bucketBags order B, q.1.card ≤ w + 1) :
    ((bucketBags order B).map
        fun q => (table (↑q.1 : Set V) q.2).encard).sum
      ≤ (order.length : ℕ∞) * ((k ^ (w + 1) : ℕ) : ℕ∞) := by
  rw [← length_bucketBags order B]
  exact elimination_order_table_total_bound _ hk halpha hwidth

end STE
