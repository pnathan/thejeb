/-
Enforcement of adaptive consistency: projective bucket elimination
preserves the solution set, and its recorded separators are the
separators of the bucket-network formalism.

`Ste.AdaptiveConsistency` proved the EASY half of Dechter's
adaptive-consistency theorem: a directionally consistent bucket network
of bounded induced width is solved greedily, backtrack-free
(`directionalConsistent_solvable`).  Left open there (docstring item
(2)) was the ENFORCEMENT half — that bucket elimination *establishes*
the consistency condition while *preserving* the solution set — and the
link between the per-instance separator bound `SepWidthLE` and the
elimination-width machinery of `Ste.Elimination` / `Ste.Treedecomp`.
This file attacks both, building on `Ste.Projection` (the ∃-step
`project`, which preserves feasibility with no substituted values) and
`Ste.Elimination` (the bucket data structure `bucketHead` /
`bucketStep`).

**Part 1 — Projective bucket elimination preserves the solution set.**
The substitutive fold of `Ste.Elimination` conditions each bucket on a
*chosen* value, so its verdict is conditional.  Here the bucket step is
the ∃-step of `Ste.Projection`: `projectBucketHead v B` joins the
bucket of `v` and *projects* `v` out — the recorded message *is* the
projection of the joined bucket (`projectBucketHead_snd`, by
definition), i.e. exactly the constraint adaptive consistency records
(`dechter1999bucket`).  The key identities:

* `joinConstraint_projectBucketStep`: one projective bucket step
  computes `project (joinConstraint B) v` — the residual network's
  joint constraint is EXACTLY the projection of the original solution
  set onto the remaining variables.  Nothing is lost (no solution
  disappears) and nothing is gained (no spurious assignment appears).
* `joinConstraint_subset_projectBucketStep`: every original solution
  survives the step (soundness of recording; needs no support
  hypothesis — `project` is inflationary).
* `exists_update_mem_of_mem_projectBucketStep`: **the step establishes
  the extension property at `v`** — every joint solution of the
  residual state extends, by changing the value at `v` alone, to a
  joint solution of the previous state.  This is directional
  consistency at the eliminated variable, in instance form: the
  recorded projection is precisely the condition under which a witness
  at `v` exists, so solution extraction never backtracks.
* `joinConstraint_projectBucketEliminate`,
  `projectBucketEliminate_nonempty_iff`, `projectBucketEliminate_decides`:
  the whole fold computes `projectEliminate`, hence preserves
  feasibility exactly, and a complete order collapses the state to the
  unconditional feasibility verdict — **projective bucket elimination
  is a complete solver** at the joint-constraint level.
* `exists_extension_of_mem_projectBucketEliminate` (**backtrack-free
  extraction**): any assignment satisfying the final state extends to a
  solution of the ORIGINAL instance by modifying only eliminated
  variables — the constructive content of completeness.

**Part 2 — Relative directional consistency suffices.**  An honest gap
surfaced by the enforcement analysis: what bucket elimination
establishes at bucket `i` is an extension property for assignments that
satisfy the EARLIER buckets (which hold the recorded messages), not for
arbitrary domain-respecting assignments as `DirectionalConsistent`
demands.  Dechter's own directional consistency is the relative notion
(`dechter2003constraint`, ch. 4).  We therefore define
`BucketRelativeConsistent` — the witness at `i.succ` is owed only to
assignments satisfying all buckets `j < i` — and prove it still implies
global solvability (`bucketRelativeConsistent_solvable`,
`bucketRelativeConsistent_solvable_from`).  The proof is a REDUCTION,
not a new induction: replace each bucket by its *guarded* form
`guardedR R i g = (earlier buckets at g) → R i g`, show the guarded
network is `SepSupported` for the fat prefix separators `prefixSep`
and *unconditionally* directionally consistent, run the existing
greedy engine, and recover the ungated solution by strong induction
(`adaptiveSolution_guardedR_iff` — the two networks have the SAME
solution set).  This closes the easy-half/enforcement mismatch: the
condition adaptive consistency actually enforces is now known to be
sufficient.

**Part 3 — The width link.**  The projective and substitutive folds
materialize IDENTICAL scope traces (`projectBucketBags_map_fst`):
scopes evolve by scope-only rules, so the width accounting of
`Ste.Treedecomp` (`AchievesWidth`, `inducedTreewidth`) applies verbatim
to the projective run (`projectBucketBags_card_le`).  Running the
DECREASING order `[n, n-1, …, 1]` on an instance over `Fin (n + 1)`
(the numbering along which `Ste.AdaptiveConsistency` states directional
consistency), the recorded message scope of the step eliminating
`i.succ` defines a separator function `runSep B : Fin n → Finset (Fin (n+1))`
with, PROVED:

* `runSep_eq_messageScope`: `runSep B i` IS the `bucketHead`-style
  message scope (`(joinScope bucket).erase i.succ`) of the state
  reached when `i.succ` is eliminated;
* `runSep_precedes`: every separator member precedes its node — the
  topological hypothesis `hsep` of `Ste.AdaptiveConsistency`;
* `runSep_widthLE`: a uniform card bound on the recorded bags gives
  `SepWidthLE (runSep B) w`;
* `runSep_link`: if the decreasing order witnesses `AchievesWidth B w`
  (every substitutive bag has `≤ w + 1` variables), then
  `SepWidthLE (runSep B) (w + 1)` and `inducedTreewidth B ≤ w` — the
  separator-size bound of the bucket-network formalism and the
  elimination width of `Ste.Treedecomp` (hence, via
  `treewidth_primalGraph_le` in `Ste.GraphTreewidth`, graph treewidth)
  measure the same quantity on the same run.

**Honest scope / what remains open.**  (1) The enforcement results are
at the JOINT-constraint level: solution-set preservation, completeness
and backtrack-free extraction are proved for `joinConstraint` of the
evolving state.  Reassembling the final state into a per-node network
`(D, sep, R)` literally satisfying `BucketRelativeConsistent D R` with
`adaptiveSet D R = joinConstraint B` (constraint-to-bucket provenance,
root-domain extraction) is NOT mechanized here; Part 2 proves the
target condition sufficient, Part 1 proves the run preserves solutions
and admits extraction, but the two are joined on paper, not in Lean.
(2) The width link is proved for the decreasing elimination order —
the order implicit in the `Fin (n + 1)` numbering of
`Ste.AdaptiveConsistency`.  For an arbitrary order one renumbers the
variables along it; that permutation argument is not mechanized.
(3) Time complexity is not modelled (only table-space bounds exist,
in `Ste.Treewidth` / `Ste.Elimination`).

References: R. Dechter and J. Pearl, *Network-based heuristics for
constraint-satisfaction problems*, Artificial Intelligence 34 (1988)
(`dechterpearl1988network` — adaptive consistency); R. Dechter, *Bucket
elimination: a unifying framework for reasoning*, Artificial
Intelligence 113 (1999) (`dechter1999bucket`); R. Dechter, *Constraint
Processing*, Morgan Kaufmann, 2003, ch. 4 (`dechter2003constraint`);
E. C. Freuder, JACM 29(1), 1982 (`freuder1982backtrack`) and JACM
32(4), 1985 (`freuder1985backtrackBounded`); H. L. Bodlaender, *A
partial k-arboretum of graphs with bounded treewidth*, TCS 209 (1998)
(`bodlaender1998arboretum`).
-/
import Ste.Projection
import Ste.Treedecomp
import Ste.AdaptiveConsistency
import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Basic

namespace STE

open Set

variable {V : Type*} {A : V → Type*} [DecidableEq V]

/-! ### Part 1: the projective bucket step -/

/-- **The projective bucket head**: join the bucket of `v` — the
constraints whose scope contains `v` — and *project* `v` out, recording
the result on the bucket bag minus `v`.  Unlike `bucketHead`
(`Ste.Elimination`), which conditions on a chosen value, this is the
∃-step of adaptive consistency (`dechter1999bucket`): the recorded
message is the full projection of the joined bucket, so no substitution
caveat is incurred. -/
def projectBucketHead (v : V) (B : List (Finset V × Set (∀ v, A v))) :
    Finset V × Set (∀ v, A v) :=
  ((joinScope (B.filter fun q => v ∈ q.1)).erase v,
    project (joinConstraint (B.filter fun q => v ∈ q.1)) v)

@[simp] theorem projectBucketHead_fst (v : V)
    (B : List (Finset V × Set (∀ v, A v))) :
    (projectBucketHead v B).1
      = (joinScope (B.filter fun q => v ∈ q.1)).erase v := rfl

/-- **The recorded message IS the projection of the joined bucket** —
definitionally.  This is the "induced constraint" adaptive consistency
records: it holds of an assignment iff SOME value at `v` extends it
into every constraint of the bucket. -/
@[simp] theorem projectBucketHead_snd (v : V)
    (B : List (Finset V × Set (∀ v, A v))) :
    (projectBucketHead v B).2
      = project (joinConstraint (B.filter fun q => v ∈ q.1)) v := rfl

/-- The projective and substitutive bucket steps record the SAME
message scope: the separator does not depend on whether the bucket is
conditioned or projected. -/
theorem projectBucketHead_fst_eq_bucketHead_fst (v : V) (a : A v)
    (B : List (Finset V × Set (∀ v, A v))) :
    (projectBucketHead v B).1 = (bucketHead ⟨v, a⟩ B).1 := rfl

/-- **One step of projective bucket elimination** at `v`: replace the
bucket of `v` by its joined, projected residue and keep the rest. -/
def projectBucketStep (v : V) (B : List (Finset V × Set (∀ v, A v))) :
    List (Finset V × Set (∀ v, A v)) :=
  projectBucketHead v B :: B.filter fun q => v ∉ q.1

theorem projectBucketStep_eq (v : V)
    (B : List (Finset V × Set (∀ v, A v))) :
    projectBucketStep v B
      = projectBucketHead v B :: B.filter fun q => v ∉ q.1 := rfl

/-- The projected message is supported on its recorded bag: the scope
accounting of `HasSupport.project`. -/
theorem projectBucketHead_support (v : V)
    {B : List (Finset V × Set (∀ v, A v))}
    (h : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V)) :
    HasSupport (projectBucketHead v B).2
      (↑(projectBucketHead v B).1 : Set V) := by
  rw [projectBucketHead_fst, projectBucketHead_snd, Finset.coe_erase]
  exact (hasSupport_joinConstraint _
    fun q hq => h q (List.mem_of_mem_filter hq)).project v

/-- **Invariant: scopes.**  A projective bucket step preserves the
invariant that every constraint is supported on its recorded scope. -/
theorem projectBucketStep_support (v : V)
    {B : List (Finset V × Set (∀ v, A v))}
    (h : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V)) :
    ∀ q ∈ projectBucketStep v B, HasSupport q.2 (↑q.1 : Set V) := by
  intro q hq
  rw [projectBucketStep_eq] at hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact projectBucketHead_support v h
  · exact h q (List.mem_of_mem_filter hq)

/-- **Invariant: elimination.**  After the projective step at `v`, no
live scope contains `v` (and scopes only shrink) — same accounting as
`bucketStep_scope_subset`. -/
theorem projectBucketStep_scope_subset (v : V)
    {B : List (Finset V × Set (∀ v, A v))} {C : Set V}
    (h : ∀ q ∈ B, (↑q.1 : Set V) ⊆ C) :
    ∀ q ∈ projectBucketStep v B, (↑q.1 : Set V) ⊆ C \ {v} := by
  intro q hq
  rw [projectBucketStep_eq] at hq
  rcases List.mem_cons.mp hq with rfl | hq
  · rw [projectBucketHead_fst, Finset.coe_erase]
    exact Set.sdiff_subset_sdiff_left (coe_joinScope_subset
      fun r hr => h r (List.mem_of_mem_filter hr))
  · have hqB : q ∈ B := List.mem_of_mem_filter hq
    have hnp : v ∉ q.1 := of_decide_eq_true (List.mem_filter.mp hq).2
    intro u hu
    refine ⟨h q hqB hu, fun he => hnp ?_⟩
    have hue : u = v := Set.mem_singleton_iff.mp he
    exact hue ▸ Finset.mem_coe.mp hu

/-! ### Solution-set preservation -/

/-- **The projective step computes the projection of the joint
constraint** — the central solution-set-preservation identity of
adaptive consistency.  The residual state's joint constraint is EXACTLY
`project (joinConstraint B) v`: recording the projected bucket loses no
solution (each original solution survives restricted to the remaining
variables) and adds none (every survivor extends into the previous
state).  The rest of the constraints need no update because they cannot
see `v`. -/
theorem joinConstraint_projectBucketStep (v : V)
    {B : List (Finset V × Set (∀ v, A v))}
    (h : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V)) :
    joinConstraint (projectBucketStep v B)
      = project (joinConstraint B) v := by
  ext f
  rw [projectBucketStep_eq, mem_joinConstraint, mem_project_iff]
  constructor
  · intro hf
    have hhead : f ∈ (projectBucketHead v B).2 :=
      hf _ (List.mem_cons.mpr (Or.inl rfl))
    rw [projectBucketHead_snd, mem_project_iff] at hhead
    obtain ⟨a, ha⟩ := hhead
    rw [mem_joinConstraint] at ha
    refine ⟨a, mem_joinConstraint.mpr fun q hqB => ?_⟩
    by_cases hv : v ∈ q.1
    · exact ha q (List.mem_filter.mpr ⟨hqB, decide_eq_true hv⟩)
    · have hq : q ∈ B.filter fun q => v ∉ q.1 :=
        List.mem_filter.mpr ⟨hqB, decide_eq_true hv⟩
      have hfq : f ∈ q.2 := hf q (List.mem_cons_of_mem _ hq)
      exact (h q hqB f (Function.update f v a) fun u hu =>
        (Function.update_of_ne (fun e : u = v =>
          hv (e ▸ Finset.mem_coe.mp hu)) a f).symm).mp hfq
  · rintro ⟨a, ha⟩
    rw [mem_joinConstraint] at ha
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [projectBucketHead_snd, mem_project_iff]
      exact ⟨a, mem_joinConstraint.mpr fun r hr =>
        ha r (List.mem_of_mem_filter hr)⟩
    · have hqB : q ∈ B := List.mem_of_mem_filter hq
      have hnp : v ∉ q.1 := of_decide_eq_true (List.mem_filter.mp hq).2
      exact (h q hqB f (Function.update f v a) fun u hu =>
        (Function.update_of_ne (fun e : u = v =>
          hnp (e ▸ Finset.mem_coe.mp hu)) a f).symm).mpr (ha q hqB)

/-- **Soundness of recording** (no support hypothesis needed): every
joint solution of the previous state satisfies the residual state —
the projected message is implied, each solution witnessing its own
value at `v`. -/
theorem joinConstraint_subset_projectBucketStep (v : V)
    (B : List (Finset V × Set (∀ v, A v))) :
    joinConstraint B ⊆ joinConstraint (projectBucketStep v B) := by
  intro f hf
  rw [mem_joinConstraint] at hf
  rw [projectBucketStep_eq, mem_joinConstraint]
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · rw [projectBucketHead_snd, mem_project_iff]
    refine ⟨f v, ?_⟩
    rw [Function.update_eq_self]
    exact mem_joinConstraint.mpr fun r hr =>
      hf r (List.mem_of_mem_filter hr)
  · exact hf q (List.mem_of_mem_filter hq)

/-- **The step establishes the extension property at `v`** — the
enforcement direction of directional consistency, in instance form:
every joint solution of the residual state extends, by changing the
value at `v` alone, to a joint solution of the previous state.  The
recorded projection is exactly the condition making the witness exist,
so solution extraction never backtracks. -/
theorem exists_update_mem_of_mem_projectBucketStep (v : V)
    {B : List (Finset V × Set (∀ v, A v))}
    (h : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V))
    {f : ∀ v, A v} (hf : f ∈ joinConstraint (projectBucketStep v B)) :
    ∃ a : A v, Function.update f v a ∈ joinConstraint B := by
  rw [joinConstraint_projectBucketStep v h] at hf
  exact mem_project_iff.mp hf

/-! ### The projective bucket fold -/

/-- Run projective bucket elimination along a list of variables. -/
def projectBucketEliminate (vs : List V)
    (B : List (Finset V × Set (∀ v, A v))) :
    List (Finset V × Set (∀ v, A v)) :=
  vs.foldl (fun B v => projectBucketStep v B) B

@[simp] theorem projectBucketEliminate_nil
    (B : List (Finset V × Set (∀ v, A v))) :
    projectBucketEliminate [] B = B := rfl

theorem projectBucketEliminate_cons (v : V) (vs : List V)
    (B : List (Finset V × Set (∀ v, A v))) :
    projectBucketEliminate (v :: vs) B
      = projectBucketEliminate vs (projectBucketStep v B) := rfl

/-- The support invariant holds along the whole projective run. -/
theorem projectBucketEliminate_support (vs : List V)
    {B : List (Finset V × Set (∀ v, A v))}
    (h : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V)) :
    ∀ q ∈ projectBucketEliminate vs B, HasSupport q.2 (↑q.1 : Set V) := by
  induction vs generalizing B with
  | nil => exact h
  | cons v vs ih => exact ih (projectBucketStep_support v h)

/-- **The fold computes projective elimination of the joint
constraint.**  Projective bucket elimination is correct: the joint
constraint of the final state is `projectEliminate` applied to the
joint constraint of the initial state — the data structure faithfully
tracks the (unsubstituted) problem. -/
theorem joinConstraint_projectBucketEliminate (vs : List V)
    {B : List (Finset V × Set (∀ v, A v))}
    (h : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V)) :
    joinConstraint (projectBucketEliminate vs B)
      = projectEliminate vs (joinConstraint B) := by
  induction vs generalizing B with
  | nil => rfl
  | cons v vs ih =>
      rw [projectBucketEliminate_cons, projectEliminate_cons,
        ih (projectBucketStep_support v h),
        joinConstraint_projectBucketStep v h]

/-- **Projective bucket elimination preserves feasibility exactly** —
the solution set is nonempty after the run iff it was before, with no
substituted values anywhere.  This is the completeness half missing
from the substitutive fold of `Ste.Elimination`. -/
theorem projectBucketEliminate_nonempty_iff (vs : List V)
    {B : List (Finset V × Set (∀ v, A v))}
    (h : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V)) :
    (joinConstraint (projectBucketEliminate vs B)).Nonempty
      ↔ (joinConstraint B).Nonempty := by
  rw [joinConstraint_projectBucketEliminate vs h,
    projectEliminate_nonempty_iff]

/-- **Projective bucket elimination is a complete solver.**  A complete
order — one whose projected variables cover every scope — collapses the
joint constraint of the final state to `univ` or `∅`, and the collapse
IS the unconditional feasibility verdict for the ORIGINAL instance:
`univ` iff feasible, `∅` iff infeasible.  Contrast
`bucketEliminate_decides` (`Ste.Elimination`), whose verdict is
relative to the substituted values of the order. -/
theorem projectBucketEliminate_decides [Nonempty (∀ v, A v)]
    {vs : List V} {B : List (Finset V × Set (∀ v, A v))}
    (hsupp : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V))
    (hcover : ∀ q ∈ B, (↑q.1 : Set V) ⊆ projected vs) :
    (joinConstraint (projectBucketEliminate vs B) = Set.univ
        ↔ (joinConstraint B).Nonempty)
      ∧ (joinConstraint (projectBucketEliminate vs B) = ∅
        ↔ joinConstraint B = ∅) := by
  rw [joinConstraint_projectBucketEliminate vs hsupp]
  exact projectEliminate_joinConstraint_decides hsupp hcover

/-- **Backtrack-free solution extraction.**  Any assignment satisfying
the final state of a projective bucket run extends to a solution of the
ORIGINAL instance by modifying only eliminated variables: walk the run
backwards, and at each step the recorded projection hands over a
witness for the eliminated variable — no choice is ever retracted.
This is the constructive content of the completeness theorem
(`dechter2003constraint`, ch. 4). -/
theorem exists_extension_of_mem_projectBucketEliminate :
    ∀ (vs : List V) {B : List (Finset V × Set (∀ v, A v))},
      (∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V)) →
      ∀ {f : ∀ v, A v}, f ∈ joinConstraint (projectBucketEliminate vs B) →
      ∃ g ∈ joinConstraint B, ∀ u, u ∉ projected vs → g u = f u := by
  intro vs
  induction vs with
  | nil =>
      intro B _ f hf
      exact ⟨f, hf, fun u _ => rfl⟩
  | cons v vs ih =>
      intro B hsupp f hf
      rw [projectBucketEliminate_cons] at hf
      obtain ⟨g, hg, hgf⟩ := ih (projectBucketStep_support v hsupp) hf
      obtain ⟨a, ha⟩ :=
        exists_update_mem_of_mem_projectBucketStep v hsupp hg
      refine ⟨Function.update g v a, ha, ?_⟩
      intro u hu
      rw [projected_cons] at hu
      have hunv : u ≠ v := fun e =>
        hu (Set.mem_union_left _ (Set.mem_singleton_iff.mpr e))
      have hunvs : u ∉ projected vs := fun hmem =>
        hu (Set.mem_union_right _ hmem)
      rw [Function.update_of_ne hunv]
      exact hgf u hunvs

/-! ### Part 2: relative directional consistency suffices

`DirectionalConsistent` (`Ste.AdaptiveConsistency`) demands a witness
at `i.succ` for EVERY domain-respecting assignment of the other
variables.  What bucket elimination actually establishes — and what
Dechter's directional consistency actually says
(`dechter2003constraint`, ch. 4) — is weaker: the witness is owed only
to assignments that satisfy the EARLIER buckets, which is where the
recorded messages live.  We prove this relative notion still yields
backtrack-free solvability, by reducing to the existing greedy engine
through the guarded network `guardedR`. -/

variable {α : Type*}

/-- **Relative (Dechter-style) directional consistency**: node `i.succ`
owes a witness only to domain-respecting assignments that already
satisfy every earlier bucket.  This is the condition adaptive
consistency establishes — weaker than `DirectionalConsistent`, which
demands witnesses unconditionally. -/
def BucketRelativeConsistent {n : ℕ} (D : Fin (n + 1) → Set α)
    (R : Fin n → (Fin (n + 1) → α) → Prop) : Prop :=
  ∀ i : Fin n, ∀ g : Fin (n + 1) → α, (∀ u, g u ∈ D u) →
    (∀ j : Fin n, j.val < i.val → R j g) →
    ∃ c ∈ D i.succ, R i (Function.update g i.succ c)

/-- Unconditional directional consistency is a special case of the
relative notion. -/
theorem DirectionalConsistent.bucketRelativeConsistent {n : ℕ}
    {D : Fin (n + 1) → Set α} {R : Fin n → (Fin (n + 1) → α) → Prop}
    (h : DirectionalConsistent D R) : BucketRelativeConsistent D R :=
  fun i g hg _ => h i g hg

/-- **The guarded network**: bucket `i` fires only on assignments
satisfying every earlier bucket.  Gating each bucket by its
predecessors turns relative consistency into unconditional directional
consistency, at the price of fat (prefix) separators. -/
def guardedR {n : ℕ} (R : Fin n → (Fin (n + 1) → α) → Prop) :
    Fin n → (Fin (n + 1) → α) → Prop :=
  fun i g => (∀ j : Fin n, j.val < i.val → R j g) → R i g

/-- **Guarding does not change the solution set**: an assignment
satisfies every guarded bucket iff it satisfies every bucket.  Backward
is trivial; forward discharges the guards by strong induction on the
node index. -/
theorem adaptiveSolution_guardedR_iff {n : ℕ}
    {D : Fin (n + 1) → Set α} {R : Fin n → (Fin (n + 1) → α) → Prop}
    {f : Fin (n + 1) → α} :
    AdaptiveSolution D (guardedR R) f ↔ AdaptiveSolution D R f := by
  constructor
  · rintro ⟨hD, hR⟩
    refine ⟨hD, fun i => ?_⟩
    have key : ∀ m : ℕ, ∀ j : Fin n, j.val ≤ m → R j f := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
          intro j hjm
          refine hR j fun k hk => ?_
          exact ih k.val (by omega) k le_rfl
    exact key i.val i le_rfl
  · rintro ⟨hD, hR⟩
    exact ⟨hD, fun i _ => hR i⟩

/-- The prefix separators: node `i.succ` sees ALL earlier nodes.  These
are the (width-`n`) separators of the guarded network — solvability
does not need a width bound, only topological order. -/
def prefixSep (n : ℕ) : Fin n → Finset (Fin (n + 1)) :=
  fun i => Finset.univ.filter fun u => u.val ≤ i.val

theorem prefixSep_precedes (n : ℕ) :
    ∀ i : Fin n, ∀ u ∈ prefixSep n i, u.val ≤ i.val := by
  intro i u hu
  exact (Finset.mem_filter.mp hu).2

/-- The guarded network is separator-dependent for the prefix
separators: every bucket `j ≤ i` reads only coordinates `≤ j + 1
≤ i + 1`, all of which lie in `prefixSep n i ∪ {i.succ}`. -/
theorem guardedR_sepSupported {n : ℕ}
    {sep : Fin n → Finset (Fin (n + 1))}
    {R : Fin n → (Fin (n + 1) → α) → Prop}
    (hsep : ∀ i : Fin n, ∀ u ∈ sep i, u.val ≤ i.val)
    (hdep : SepSupported sep R) :
    SepSupported (prefixSep n) (guardedR R) := by
  intro i g g' hs hsucc
  have hval : ∀ u : Fin (n + 1), u.val ≤ i.val → g u = g' u := fun u hu =>
    hs u (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩)
  have hRj : ∀ j : Fin n, j.val ≤ i.val → (R j g ↔ R j g') := by
    intro j hj
    apply hdep j g g'
    · intro u hu
      exact hval u (le_trans (hsep j u hu) hj)
    · rcases lt_or_eq_of_le hj with hlt | heq
      · exact hval j.succ (by rw [Fin.val_succ]; omega)
      · have hje : j.succ = i.succ := by
          apply Fin.ext
          rw [Fin.val_succ, Fin.val_succ, heq]
        rw [hje]
        exact hsucc
  show ((∀ k : Fin n, k.val < i.val → R k g) → R i g)
    ↔ ((∀ k : Fin n, k.val < i.val → R k g') → R i g')
  exact imp_congr
    (forall_congr' fun k => imp_congr_right fun hk => hRj k (le_of_lt hk))
    (hRj i le_rfl)

/-- **Relative consistency makes the guarded network unconditionally
directionally consistent**: if the assignment satisfies the earlier
buckets, the relative witness serves; if not, any domain value serves
vacuously — the guard cannot be discharged, because an update at
`i.succ` is invisible to the earlier buckets. -/
theorem guardedR_directionalConsistent {n : ℕ}
    {D : Fin (n + 1) → Set α} {sep : Fin n → Finset (Fin (n + 1))}
    {R : Fin n → (Fin (n + 1) → α) → Prop}
    (hsep : ∀ i : Fin n, ∀ u ∈ sep i, u.val ≤ i.val)
    (hdep : SepSupported sep R)
    (hRC : BucketRelativeConsistent D R)
    (hne : ∀ u, (D u).Nonempty) :
    DirectionalConsistent D (guardedR R) := by
  intro i g hg
  by_cases hall : ∀ j : Fin n, j.val < i.val → R j g
  · obtain ⟨c, hc, hRc⟩ := hRC i g hg hall
    exact ⟨c, hc, fun _ => hRc⟩
  · obtain ⟨c, hc⟩ := hne i.succ
    refine ⟨c, hc, ?_⟩
    intro hant
    exfalso
    apply hall
    intro j hj
    have h1 : ∀ u ∈ sep j, g u = Function.update g i.succ c u := by
      intro u hu
      have hu' := hsep j u hu
      have hne' : u ≠ i.succ := by
        intro e
        have he := congrArg Fin.val e
        rw [Fin.val_succ] at he
        omega
      exact (Function.update_of_ne hne' c g).symm
    have h2 : g j.succ = Function.update g i.succ c j.succ := by
      have hne' : j.succ ≠ i.succ := by
        intro e
        have he := congrArg Fin.val e
        rw [Fin.val_succ, Fin.val_succ] at he
        omega
      exact (Function.update_of_ne hne' c g).symm
    exact (hdep j g (Function.update g i.succ c) h1 h2).mpr (hant j hj)

/-- **Backtrack-free search from RELATIVE directional consistency,
through a prescribed root value** — the honest output condition of
adaptive consistency suffices.  Reduce to the unconditional theorem of
`Ste.AdaptiveConsistency` via the guarded network: same solution set
(`adaptiveSolution_guardedR_iff`), prefix separators, unconditional
consistency (`guardedR_directionalConsistent`). -/
theorem bucketRelativeConsistent_solvable_from {n : ℕ}
    (D : Fin (n + 1) → Set α) (sep : Fin n → Finset (Fin (n + 1)))
    (R : Fin n → (Fin (n + 1) → α) → Prop)
    (hsep : ∀ i : Fin n, ∀ u ∈ sep i, u.val ≤ i.val)
    (hdep : SepSupported sep R)
    (hRC : BucketRelativeConsistent D R)
    (hne : ∀ u, (D u).Nonempty) :
    ∀ a ∈ D 0, ∃ f, AdaptiveSolution D R f ∧ f 0 = a := by
  intro a ha
  obtain ⟨f, hf, hf0⟩ := directionalConsistent_solvable_from D
    (prefixSep n) (guardedR R) (prefixSep_precedes n)
    (guardedR_sepSupported hsep hdep)
    (guardedR_directionalConsistent hsep hdep hRC hne) hne a ha
  exact ⟨f, adaptiveSolution_guardedR_iff.mp hf, hf0⟩

/-- **The relative adaptive-consistency theorem**: a nonempty bucket
network that is directionally consistent RELATIVE to its earlier
buckets — the condition bucket elimination actually establishes — has a
global solution.  This closes the gap between the sufficiency half
proved in `Ste.AdaptiveConsistency` (which assumed unconditional
witnesses) and the enforcement half (which only provides relative
ones). -/
theorem bucketRelativeConsistent_solvable {n : ℕ}
    {D : Fin (n + 1) → Set α} {sep : Fin n → Finset (Fin (n + 1))}
    {R : Fin n → (Fin (n + 1) → α) → Prop}
    (hsep : ∀ i : Fin n, ∀ u ∈ sep i, u.val ≤ i.val)
    (hdep : SepSupported sep R)
    (hRC : BucketRelativeConsistent D R)
    (hne : ∀ u, (D u).Nonempty) :
    ∃ f, AdaptiveSolution D R f := by
  obtain ⟨a, ha⟩ := hne 0
  obtain ⟨f, hf, -⟩ :=
    bucketRelativeConsistent_solvable_from D sep R hsep hdep hRC hne a ha
  exact ⟨f, hf⟩

end STE

namespace STE

open Set

variable {V : Type*} {A : V → Type*} [DecidableEq V]

/-! ### Part 3: the width link

The scope trace of a bucket run is blind to whether buckets are
conditioned or projected: filters and message scopes are computed from
scopes alone.  So the width accounting of `Ste.Treedecomp`
(`AchievesWidth`, `inducedTreewidth`), stated for the substitutive
fold, transfers verbatim to the projective one; and along the
decreasing order on `Fin (n + 1)` the recorded message scopes are
exactly the separators of the bucket-network formalism of
`Ste.AdaptiveConsistency`. -/

/-- The trace of a projective bucket run: the (bag, message) pair
materialized at each step — the projective `bucketBags`. -/
def projectBucketBags : List V → List (Finset V × Set (∀ v, A v))
    → List (Finset V × Set (∀ v, A v))
  | [], _ => []
  | v :: vs, B =>
      projectBucketHead v B :: projectBucketBags vs (projectBucketStep v B)

@[simp] theorem projectBucketBags_nil
    (B : List (Finset V × Set (∀ v, A v))) :
    projectBucketBags [] B = [] := rfl

theorem projectBucketBags_cons (v : V) (vs : List V)
    (B : List (Finset V × Set (∀ v, A v))) :
    projectBucketBags (v :: vs) B
      = projectBucketHead v B
          :: projectBucketBags vs (projectBucketStep v B) := rfl

theorem length_projectBucketBags (vs : List V)
    (B : List (Finset V × Set (∀ v, A v))) :
    (projectBucketBags vs B).length = vs.length := by
  induction vs generalizing B with
  | nil => rfl
  | cons v vs ih => simp [projectBucketBags_cons, ih]

private theorem getD_mem_of_lt {β : Type*} :
    ∀ {l : List β} {i : ℕ} {d : β}, i < l.length → l.getD i d ∈ l
  | _ :: _, 0, _, _ => List.mem_cons_self
  | a :: _, _ + 1, _, h =>
      List.mem_cons_of_mem a (getD_mem_of_lt (Nat.lt_of_succ_lt_succ h))

/-- Equal scope columns filter equally: the fst-trace of a filtered
bucket list depends only on the fst-trace of the list (positive
occurrence filter). -/
private theorem map_fst_filter_pos {B B' : List (Finset V × Set (∀ v, A v))}
    (h : B.map Prod.fst = B'.map Prod.fst) (v : V) :
    (B.filter fun q => v ∈ q.1).map Prod.fst
      = (B'.filter fun q => v ∈ q.1).map Prod.fst := by
  induction B generalizing B' with
  | nil =>
      cases B' with
      | nil => rfl
      | cons r B' => simp at h
  | cons q B ih =>
      cases B' with
      | nil => simp at h
      | cons r B' =>
          rw [List.map_cons, List.map_cons] at h
          injection h with h1 h2
          by_cases hv : v ∈ q.1
          · rw [List.filter_cons_of_pos (by simpa using hv),
              List.filter_cons_of_pos (by simpa [← h1] using hv),
              List.map_cons, List.map_cons, h1, ih h2]
          · rw [List.filter_cons_of_neg (by simpa using hv),
              List.filter_cons_of_neg (by simpa [← h1] using hv), ih h2]

/-- Negative-occurrence version of `map_fst_filter_pos`. -/
private theorem map_fst_filter_neg {B B' : List (Finset V × Set (∀ v, A v))}
    (h : B.map Prod.fst = B'.map Prod.fst) (v : V) :
    (B.filter fun q => v ∉ q.1).map Prod.fst
      = (B'.filter fun q => v ∉ q.1).map Prod.fst := by
  induction B generalizing B' with
  | nil =>
      cases B' with
      | nil => rfl
      | cons r B' => simp at h
  | cons q B ih =>
      cases B' with
      | nil => simp at h
      | cons r B' =>
          rw [List.map_cons, List.map_cons] at h
          injection h with h1 h2
          by_cases hv : v ∈ q.1
          · rw [List.filter_cons_of_neg (by simpa using hv),
              List.filter_cons_of_neg (by simpa [← h1] using hv), ih h2]
          · rw [List.filter_cons_of_pos (by simpa using hv),
              List.filter_cons_of_pos (by simpa [← h1] using hv),
              List.map_cons, List.map_cons, h1, ih h2]

/-- The join scope depends only on the scope column. -/
private theorem joinScope_congr {B B' : List (Finset V × Set (∀ v, A v))}
    (h : B.map Prod.fst = B'.map Prod.fst) :
    joinScope B = joinScope B' := by
  induction B generalizing B' with
  | nil =>
      cases B' with
      | nil => rfl
      | cons r B' => simp at h
  | cons q B ih =>
      cases B' with
      | nil => simp at h
      | cons r B' =>
          rw [List.map_cons, List.map_cons] at h
          injection h with h1 h2
          rw [joinScope_cons, joinScope_cons, h1, ih h2]

/-- **Projective and substitutive runs have identical scope traces.**
Scopes evolve by scope-only rules — which constraints join the bucket
and which variables the message reads never depend on the constraint
components, hence not on whether the bucket is conditioned
(`bucketHead`) or projected (`projectBucketHead`).  The width
accounting of `Ste.Elimination` / `Ste.Treedecomp` therefore applies
verbatim to the projective fold. -/
theorem projectBucketBags_map_fst (order : List ((v : V) × A v)) :
    ∀ {B B' : List (Finset V × Set (∀ v, A v))},
      B.map Prod.fst = B'.map Prod.fst →
      (projectBucketBags (order.map Sigma.fst) B).map Prod.fst
        = (bucketBags order B').map Prod.fst := by
  induction order with
  | nil => intro B B' _; rfl
  | cons p order ih =>
      intro B B' h
      have hhead : (projectBucketHead p.1 B).1 = (bucketHead p B').1 := by
        rw [projectBucketHead_fst, bucketHead_fst,
          joinScope_congr (map_fst_filter_pos h p.1)]
      have hstep : (projectBucketStep p.1 B).map Prod.fst
          = (bucketStep p B').map Prod.fst := by
        rw [projectBucketStep_eq, bucketStep_eq]
        simp only [List.map_cons]
        rw [hhead, map_fst_filter_neg h p.1]
      simp only [List.map_cons, projectBucketBags_cons, bucketBags_cons]
      rw [hhead, ih hstep]

/-- **Width transfer**: a uniform bag bound on the substitutive run
(the quantity minimized by `inducedTreewidth`) bounds every projective
message scope of the same order. -/
theorem projectBucketBags_card_le {order : List ((v : V) × A v)}
    {B : List (Finset V × Set (∀ v, A v))} {w : ℕ}
    (hw : ∀ q ∈ bucketBags order B, q.1.card ≤ w) :
    ∀ q ∈ projectBucketBags (order.map Sigma.fst) B, q.1.card ≤ w := by
  intro q hq
  have hmap := projectBucketBags_map_fst order
    (rfl : B.map Prod.fst = B.map Prod.fst)
  have hq1 : q.1 ∈ (bucketBags order B).map Prod.fst := by
    rw [← hmap]
    exact List.mem_map.mpr ⟨q, hq, rfl⟩
  obtain ⟨r, hr, hrq⟩ := List.mem_map.mp hq1
  rw [← hrq]
  exact hw r hr

/-- **Per-step scope bound for the trace.**  At step `k` of a
projective run, the recorded message scope avoids every variable
processed so far (including the step's own variable) — the trace form
of the elimination invariant. -/
theorem projectBucketBags_getD_scope :
    ∀ (vs : List V) {B : List (Finset V × Set (∀ v, A v))} {C : Set V},
      (∀ q ∈ B, (↑q.1 : Set V) ⊆ C) → ∀ k, k < vs.length →
      (↑((projectBucketBags vs B).getD k (∅, ∅)).1 : Set V)
        ⊆ C \ projected (vs.take (k + 1)) := by
  intro vs
  induction vs with
  | nil =>
      intro B C _ k hk
      simp at hk
  | cons v vs ih =>
      intro B C h k hk
      cases k with
      | zero =>
          rw [projectBucketBags_cons, List.getD_cons_zero,
            List.take_succ_cons, List.take_zero, projected_cons,
            projected_nil, Set.union_empty]
          exact projectBucketStep_scope_subset v h _
            (by rw [projectBucketStep_eq]; exact List.mem_cons_self)
      | succ k =>
          rw [projectBucketBags_cons, List.getD_cons_succ,
            List.take_succ_cons, projected_cons]
          have hk' : k < vs.length := by
            simp only [List.length_cons] at hk
            omega
          intro u hu
          have h2 := ih (projectBucketStep_scope_subset v h) k hk' hu
          refine ⟨h2.1.1, fun hmem => ?_⟩
          rcases (Set.mem_union u {v} (projected (vs.take (k + 1)))).mp hmem
            with hv | hp
          · exact h2.1.2 hv
          · exact h2.2 hp

/-- The trace entry at position `k` is the projective bucket head of
the intermediate state, at the `k`-th variable of the order. -/
theorem projectBucketBags_getD_eq (d : V) :
    ∀ (vs : List V) (B : List (Finset V × Set (∀ v, A v))) (k : ℕ),
      k < vs.length →
      (projectBucketBags vs B).getD k (∅, ∅)
        = projectBucketHead (vs.getD k d)
            (projectBucketEliminate (vs.take k) B) := by
  intro vs
  induction vs with
  | nil =>
      intro B k hk
      simp at hk
  | cons v vs ih =>
      intro B k hk
      cases k with
      | zero =>
          rw [projectBucketBags_cons, List.getD_cons_zero,
            List.getD_cons_zero, List.take_zero, projectBucketEliminate_nil]
      | succ k =>
          rw [projectBucketBags_cons, List.getD_cons_succ,
            List.getD_cons_succ, List.take_succ_cons,
            projectBucketEliminate_cons]
          exact ih (projectBucketStep v B) k
            (by simp only [List.length_cons] at hk; omega)

/-! ### The decreasing order on `Fin (n + 1)` -/

/-- The decreasing elimination order `[n, n - 1, …, 1]` on
`Fin (n + 1)`: eliminate the last node first, keep the root.  This is
the order implicit in the numbering of `Ste.AdaptiveConsistency`, where
bucket `i` belongs to node `i.succ` and separators must precede their
node. -/
def decreasingOrder (n : ℕ) : List (Fin (n + 1)) :=
  (List.range n).map fun k => ⟨n - k, by omega⟩

@[simp] theorem length_decreasingOrder (n : ℕ) :
    (decreasingOrder n).length = n := by
  simp [decreasingOrder]

/-- Membership in a prefix of the decreasing order is a threshold: the
first `k + 1` steps process exactly the variables of value `≥ n - k`. -/
theorem mem_take_decreasingOrder_iff {n k : ℕ} (hk : k < n)
    {u : Fin (n + 1)} :
    u ∈ (decreasingOrder n).take (k + 1) ↔ n - k ≤ u.val := by
  unfold decreasingOrder
  rw [← List.map_take, List.take_range, Nat.min_eq_left (by omega)]
  constructor
  · intro hu
    obtain ⟨j, hj, hju⟩ := List.mem_map.mp hu
    have hjlt : j < k + 1 := List.mem_range.mp hj
    have hval : u.val = n - j := by rw [← hju]
    omega
  · intro hu
    refine List.mem_map.mpr ⟨n - u.val, List.mem_range.mpr (by omega), ?_⟩
    apply Fin.ext
    have := u.isLt
    show n - (n - u.val) = u.val
    omega

/-- Step `n - 1 - i` of the decreasing order eliminates node
`i.succ`. -/
theorem decreasingOrder_getD {n : ℕ} (i : Fin n) :
    (decreasingOrder n).getD (n - 1 - i.val) 0 = i.succ := by
  have hi := i.isLt
  have hk : n - 1 - i.val < (decreasingOrder n).length := by
    rw [length_decreasingOrder]
    omega
  rw [List.getD_eq_getElem _ _ hk]
  simp only [decreasingOrder, List.getElem_map, List.getElem_range]
  apply Fin.ext
  simp only [Fin.val_succ]
  show n - (n - 1 - i.val) = i.val + 1
  omega

/-! ### The recorded separators of the decreasing run -/

variable {α : Type*}

/-- **The separator function recorded by the projective decreasing
run**: `runSep B i` is the message scope materialized at the step that
eliminates node `i.succ`.  These are the separators `sep` of the
bucket-network formalism of `Ste.AdaptiveConsistency`, produced by the
algorithm rather than postulated. -/
def runSep {n : ℕ}
    (B : List (Finset (Fin (n + 1)) × Set (Fin (n + 1) → α))) :
    Fin n → Finset (Fin (n + 1)) :=
  fun i =>
    ((projectBucketBags (decreasingOrder n) B).getD
      (n - 1 - i.val) (∅, ∅)).1

/-- `runSep B i` is literally the `bucketHead`-style message scope —
`(joinScope bucket).erase i.succ` — of the intermediate state reached
when `i.succ` is eliminated. -/
theorem runSep_eq_messageScope {n : ℕ}
    (B : List (Finset (Fin (n + 1)) × Set (Fin (n + 1) → α)))
    (i : Fin n) :
    runSep B i
      = (projectBucketHead i.succ
          (projectBucketEliminate
            ((decreasingOrder n).take (n - 1 - i.val)) B)).1 := by
  have hi := i.isLt
  have hk : n - 1 - i.val < (decreasingOrder n).length := by
    rw [length_decreasingOrder]
    omega
  show ((projectBucketBags (decreasingOrder n) B).getD
      (n - 1 - i.val) (∅, ∅)).1 = _
  rw [projectBucketBags_getD_eq (0 : Fin (n + 1)) (decreasingOrder n) B
    (n - 1 - i.val) hk, decreasingOrder_getD i]

/-- **The recorded separators are topologically ordered**: every member
of `runSep B i` precedes node `i.succ`.  This is the hypothesis `hsep`
of the solvability theorems of `Ste.AdaptiveConsistency` — established
by the run, not assumed: when `i.succ` is eliminated, all later nodes
are already gone from every live scope, and the message scope excludes
`i.succ` itself. -/
theorem runSep_precedes {n : ℕ}
    (B : List (Finset (Fin (n + 1)) × Set (Fin (n + 1) → α))) :
    ∀ i : Fin n, ∀ u ∈ runSep B i, u.val ≤ i.val := by
  intro i u hu
  have hi := i.isLt
  have hk : n - 1 - i.val < (decreasingOrder n).length := by
    rw [length_decreasingOrder]
    omega
  have hsub := projectBucketBags_getD_scope (decreasingOrder n)
    (B := B) (C := Set.univ) (fun q _ => Set.subset_univ _)
    (n - 1 - i.val) hk
  have hu' := hsub (Finset.mem_coe.mpr hu)
  have hnot : u ∉ (decreasingOrder n).take (n - 1 - i.val + 1) :=
    fun hmem => hu'.2 hmem
  by_contra hgt
  push_neg at hgt
  apply hnot
  rw [mem_take_decreasingOrder_iff (by omega : n - 1 - i.val < n)]
  omega

/-- **The recorded separators obey the width bound of the run**: if
every message scope the projective decreasing run materializes has at
most `w` variables, then `SepWidthLE (runSep B) w` — the per-instance
separator bound of `Ste.AdaptiveConsistency`, discharged by the
algorithm's own trace. -/
theorem runSep_widthLE {n : ℕ}
    {B : List (Finset (Fin (n + 1)) × Set (Fin (n + 1) → α))} {w : ℕ}
    (h : ∀ q ∈ projectBucketBags (decreasingOrder n) B, q.1.card ≤ w) :
    SepWidthLE (runSep B) w := by
  intro i
  have hi := i.isLt
  have hk : n - 1 - i.val
      < (projectBucketBags (decreasingOrder n) B).length := by
    rw [length_projectBucketBags, length_decreasingOrder]
    omega
  exact h _ (getD_mem_of_lt hk)

/-- **The width link, assembled.**  Let the decreasing order (with any
substituted values) be complete for `B` and materialize only message
scopes of at most `w + 1` variables — i.e. witness `AchievesWidth B w`
in the sense of `Ste.Treedecomp`.  Then the separators recorded by the
projective run form a bucket-network separator function in the sense of
`Ste.AdaptiveConsistency`: topologically ordered (`hsep`) and of width
`SepWidthLE (runSep B) (w + 1)`; and the instance's induced treewidth
satisfies `inducedTreewidth B ≤ w`.  Via `treewidth_primalGraph_le`
(`Ste.GraphTreewidth`), all three width measures — the separator bound
of the bucket-network formalism, the elimination width of
`Ste.Treedecomp`, and (up to the fixed offset) the treewidth of the
primal graph — are controlled by the same run. -/
theorem runSep_link {n : ℕ} [Nonempty α] {w : ℕ}
    (B : List (Finset (Fin (n + 1)) × Set (Fin (n + 1) → α)))
    (order : List ((v : Fin (n + 1)) × α))
    (hfst : order.map Sigma.fst = decreasingOrder n)
    (hcov : ∀ q ∈ B, (↑q.1 : Set (Fin (n + 1))) ⊆ eliminated order)
    (hw : ∀ q ∈ bucketBags order B, q.1.card ≤ w + 1) :
    (∀ i : Fin n, ∀ u ∈ runSep B i, u.val ≤ i.val)
      ∧ SepWidthLE (runSep B) (w + 1)
      ∧ inducedTreewidth B ≤ w := by
  refine ⟨runSep_precedes B, ?_, inducedTreewidth_le ⟨order, hcov, hw⟩⟩
  apply runSep_widthLE
  have h := projectBucketBags_card_le hw
  rw [hfst] at h
  exact h

end STE
