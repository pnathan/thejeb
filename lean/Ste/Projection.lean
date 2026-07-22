/-
Projective (existential) elimination: feasibility without substitution.

`Ste.Conditioning` eliminates a variable by *fixing* it (`condition T v
a`), and `Ste.Elimination` folds that step into bucket elimination
(`bucketEliminate_decides`) — but the resulting decision is
*conditional* on the chosen values: the fold decides feasibility of the
instance *given* the substituted assignment.  This file removes that
substitution caveat by eliminating variables *existentially*: `project
T v` keeps an assignment iff *some* value of `v` extends it into `T`.

Main results:

* `HasSupport.project`: projection removes `v` from the support — the
  same scope accounting as conditioning.
* `project_nonempty_iff`: **projection preserves nonemptiness
  exactly** — `(project T v).Nonempty ↔ T.Nonempty`, with no chosen
  value.  This is the point: the ∃-step decides feasibility
  unconditionally.
* `projectEliminate_nonempty_iff`: the whole projective elimination
  fold preserves nonemptiness — feasibility of the original instance is
  read off the fully eliminated residue.
* `projectEliminate_eq_univ_or_empty`,
  `projectEliminate_decides_feasibility`: a complete elimination list
  (one covering a support) collapses the constraint to `univ` or `∅`,
  and the collapse *is* the unconditional feasibility answer:
  `univ ↔ T.Nonempty`, `∅ ↔ T = ∅`.
* `projectEliminate_joinConstraint_decides`: instantiated at the joint
  constraint of a bucket list — bucket elimination by projection
  decides unconditional feasibility of the whole instance.
* `project_eq_iUnion_condition`: the ∃-step is the union of all
  conditionings — projective elimination is conditioning summed over
  the alphabet, tying this file to the machinery of `Ste.Elimination`.

Reference: R. Dechter, "Bucket elimination: a unifying framework for
reasoning," Artificial Intelligence 113 (1999) — adaptive consistency,
where the bucket step is projection (∃), not substitution.
-/
import Ste.Elimination

namespace STE

open Set

variable {V : Type*} {A : V → Type*} [DecidableEq V]

/-! ### The projection step -/

/-- Projecting a variable out of a constraint: `f` survives iff *some*
value at `v` extends it into `T`.  This is existential (∃-)elimination —
no value is chosen, so no substitution caveat is incurred. -/
def project (T : Set (∀ v, A v)) (v : V) : Set (∀ v, A v) :=
  {f | ∃ a : A v, Function.update f v a ∈ T}

theorem mem_project_iff {T : Set (∀ v, A v)} {v : V} {f : ∀ v, A v} :
    f ∈ project T v ↔ ∃ a : A v, Function.update f v a ∈ T :=
  Iff.rfl

/-- Projection is monotone in the constraint. -/
theorem project_mono {T U : Set (∀ v, A v)} (h : T ⊆ U) (v : V) :
    project T v ⊆ project U v :=
  fun _ ⟨a, ha⟩ => ⟨a, h ha⟩

/-- Projection is inflationary: every satisfying assignment survives
projection (witness its own value). -/
theorem subset_project (T : Set (∀ v, A v)) (v : V) :
    T ⊆ project T v := fun f hf =>
  mem_project_iff.mpr ⟨f v, by rwa [Function.update_eq_self]⟩

@[simp] theorem project_empty (v : V) :
    project (∅ : Set (∀ v, A v)) v = ∅ := by
  ext f
  simp [mem_project_iff]

/-- **Projection is the union of all conditionings**: the ∃-step is
substitution summed over the whole alphabet.  Everything the
conditioning machinery of `Ste.Elimination` computes value-by-value,
projection aggregates. -/
theorem project_eq_iUnion_condition (T : Set (∀ v, A v)) (v : V) :
    project T v = ⋃ a : A v, condition T v a := by
  ext f
  simp only [mem_project_iff, Set.mem_iUnion, mem_condition_iff]

/-- Each conditioning is below the projection. -/
theorem condition_subset_project (T : Set (∀ v, A v)) (v : V) (a : A v) :
    condition T v a ⊆ project T v :=
  fun _ hf => mem_project_iff.mpr ⟨a, hf⟩

/-- **Projection shrinks scopes.**  If `T` is supported on `σ`, the
projected constraint is supported on `σ \ {v}`: the eliminated variable
leaves the constraint hypergraph, exactly as with conditioning. -/
theorem HasSupport.project {T : Set (∀ v, A v)} {σ : Set V}
    (hT : HasSupport T σ) (v : V) :
    HasSupport (STE.project T v) (σ \ {v}) := by
  intro f g hfg
  show (∃ a : A v, Function.update f v a ∈ T)
    ↔ ∃ a : A v, Function.update g v a ∈ T
  refine exists_congr fun a => hT _ _ fun w hw => ?_
  show Function.update f v a w = Function.update g v a w
  by_cases hwv : w = v
  · subst hwv
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hwv, Function.update_of_ne hwv]
    exact hfg w ⟨hw, hwv⟩

/-! ### The unconditional feasibility decision -/

/-- **Projection preserves nonemptiness exactly.**  The projected
constraint is feasible iff the original one is — with *no* chosen
value.  Backward: a satisfying `g` survives as its own witness
(`Function.update g v (g v) = g`).  Forward: any survivor extends to a
satisfying assignment by definition.  This is the ∃-step's advantage
over conditioning: feasibility is decided unconditionally. -/
theorem project_nonempty_iff (T : Set (∀ v, A v)) (v : V) :
    (project T v).Nonempty ↔ T.Nonempty := by
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨a, ha⟩ := mem_project_iff.mp hf
    exact ⟨Function.update f v a, ha⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, mem_project_iff.mpr ⟨g v, by rwa [Function.update_eq_self]⟩⟩

/-! ### The projective elimination fold -/

/-- Run projective elimination: fold `project` over a list of
variables.  Unlike `eliminate`, the list carries no values — nothing is
substituted. -/
def projectEliminate (vs : List V) (T : Set (∀ v, A v)) :
    Set (∀ v, A v) :=
  vs.foldl (fun S v => project S v) T

@[simp] theorem projectEliminate_nil (T : Set (∀ v, A v)) :
    projectEliminate [] T = T := rfl

theorem projectEliminate_cons (v : V) (vs : List V)
    (T : Set (∀ v, A v)) :
    projectEliminate (v :: vs) T = projectEliminate vs (project T v) :=
  rfl

/-- The set of variables a list projects out. -/
def projected (vs : List V) : Set V :=
  {u | u ∈ vs}

@[simp] theorem projected_nil : projected ([] : List V) = ∅ := by
  ext u
  simp [projected]

theorem projected_cons (v : V) (vs : List V) :
    projected (v :: vs) = {v} ∪ projected vs := by
  ext u
  simp [projected, List.mem_cons]

/-- **Scope accounting for a whole projective run.**  Projecting out a
list of variables removes them all from the support: the residue lives
on `σ \ projected vs`. -/
theorem HasSupport.projectEliminate {T : Set (∀ v, A v)} {σ : Set V}
    (hT : HasSupport T σ) (vs : List V) :
    HasSupport (STE.projectEliminate vs T) (σ \ projected vs) := by
  induction vs generalizing T σ with
  | nil => simpa using hT
  | cons v vs ih =>
      rw [projectEliminate_cons, projected_cons]
      have h := ih (hT.project v)
      rwa [Set.sdiff_sdiff] at h

/-- **The projective fold preserves nonemptiness exactly** — by
induction on `project_nonempty_iff`.  Feasibility of the original
constraint is decided by the fully projected residue, with no
substituted values anywhere. -/
theorem projectEliminate_nonempty_iff (vs : List V)
    (T : Set (∀ v, A v)) :
    (projectEliminate vs T).Nonempty ↔ T.Nonempty := by
  induction vs generalizing T with
  | nil => exact Iff.rfl
  | cons v vs ih =>
      rw [projectEliminate_cons, ih, project_nonempty_iff]

/-! ### Complete elimination decides the instance unconditionally -/

/-- **A complete projective run collapses the constraint.**  If the
projected variables cover a support of `T`, the residue is supported on
`∅`, hence trivial: `univ` or `∅`. -/
theorem projectEliminate_eq_univ_or_empty {T : Set (∀ v, A v)}
    {σ : Set V} (hT : HasSupport T σ) {vs : List V}
    (hcover : σ ⊆ projected vs) :
    projectEliminate vs T = Set.univ ∨ projectEliminate vs T = ∅ := by
  have h := hT.projectEliminate vs
  rw [Set.sdiff_eq_empty.mpr hcover] at h
  exact (hasSupport_empty_iff _).mp h

/-- **Projective elimination decides feasibility unconditionally.**
Run a complete elimination list on a constraint over a nonempty
assignment space: the residue is `univ` exactly when the instance is
feasible and `∅` exactly when it is infeasible.  Contrast
`bucketEliminate_decides`, whose `univ`/`∅` verdict is relative to the
substituted values `p.2` of the order: here there are no values, so the
verdict is about `T` itself. -/
theorem projectEliminate_decides_feasibility [Nonempty (∀ v, A v)]
    {T : Set (∀ v, A v)} {σ : Set V} (hT : HasSupport T σ)
    {vs : List V} (hcover : σ ⊆ projected vs) :
    (projectEliminate vs T = Set.univ ↔ T.Nonempty)
      ∧ (projectEliminate vs T = ∅ ↔ T = ∅) := by
  have hdec := projectEliminate_eq_univ_or_empty hT hcover
  have hne := projectEliminate_nonempty_iff vs T
  constructor
  · constructor
    · intro h
      rw [← hne, h]
      exact Set.univ_nonempty
    · intro h
      rcases hdec with h1 | h1
      · exact h1
      · rw [← hne, h1] at h
        exact absurd h Set.not_nonempty_empty
  · constructor
    · intro h
      rw [← Set.not_nonempty_iff_eq_empty, ← hne, h]
      exact Set.not_nonempty_empty
    · intro h
      rcases hdec with h1 | h1
      · exfalso
        have hne' : (projectEliminate vs T).Nonempty := by
          rw [h1]
          exact Set.univ_nonempty
        rw [hne, h] at hne'
        exact Set.not_nonempty_empty hne'
      · exact h1

/-! ### Bucket elimination by projection: the joint constraint -/

/-- **Projective bucket elimination preserves joint feasibility
exactly.**  For any bucket list `B` and any elimination list, the
projected joint constraint is nonempty iff the joint constraint is —
the instance-level form of `projectEliminate_nonempty_iff`, with no
substitution caveat. -/
theorem projectEliminate_joinConstraint_nonempty_iff (vs : List V)
    (B : List (Finset V × Set (∀ v, A v))) :
    (projectEliminate vs (joinConstraint B)).Nonempty
      ↔ (joinConstraint B).Nonempty :=
  projectEliminate_nonempty_iff vs (joinConstraint B)

/-- **Bucket elimination by projection decides unconditional
feasibility of the whole instance.**  If every constraint in the bucket
list is supported on its recorded scope and the elimination list covers
every scope, projecting out the list collapses the joint constraint to
`univ` or `∅`, and the collapse is the feasibility answer itself:
`univ` iff the instance is feasible, `∅` iff it is not. -/
theorem projectEliminate_joinConstraint_decides [Nonempty (∀ v, A v)]
    {B : List (Finset V × Set (∀ v, A v))} {vs : List V}
    (hsupp : ∀ q ∈ B, HasSupport q.2 (↑q.1 : Set V))
    (hcover : ∀ q ∈ B, (↑q.1 : Set V) ⊆ projected vs) :
    (projectEliminate vs (joinConstraint B) = Set.univ
        ↔ (joinConstraint B).Nonempty)
      ∧ (projectEliminate vs (joinConstraint B) = ∅
        ↔ joinConstraint B = ∅) :=
  projectEliminate_decides_feasibility
    (hasSupport_joinConstraint B hsupp) (coe_joinScope_subset hcover)

end STE
