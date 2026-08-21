/-
Semijoin enforcement of pairwise consistency — the algorithmic half of
the Beeri–Fagin–Maier–Yannakakis / Yannakakis acyclic-join guarantee.

`Ste.AcyclicSolvability` proved the *declarative* half of BFMY:
on a GYO-reducible (α-acyclic) hypergraph, pairwise-consistent nonempty
edge relations admit a global solution
(`gyoReducible_pairwiseConsistent_solvable`).  Its honest-residue note
(3) recorded that the *enforcement* of `PairwiseConsistent` by a
semijoin program was not modelled.  This file closes that item: the
semijoin pass is modelled as an actual operation on extensional tables,
and it is proved to do its job.

Representation.  A local relation is a set of full assignments,
`Rel : Fin m → Set (Fin (n + 1) → α)`, each `Rel k` supported on its
hyperedge scope `E k` in the sense of the codebase's `HasSupport`
(`Ste.Support`), so `Rel k` *is* its table on `E k`
(`HasSupport.eq_preimage_table` in `Ste.Treewidth`).  The bridge to the
propositional idiom of `Ste.AcyclicSolvability` is `fun k g => g ∈ Rel k`
(`edgeSupported_of_hasSupport`).

Contents:

* `semijoinReduced E Rel k k'` — the semijoin `Rel k ⋉ Rel k'`: the
  tuples of `Rel k` that match some tuple of `Rel k'` on the shared
  attributes `E k ∩ E k'`.  `semijoinStep E Rel k k'` performs one
  reduction, updating table `k` only (`Function.update`).
* Soundness of one step: only `Rel k` shrinks and only downward
  (`semijoinStep_subset`), the joint solution set `⋂ j, Rel j` is
  untouched (`semijoinStep_iInter` — a removed tuple extends to no
  global solution), and supports are preserved
  (`hasSupport_semijoinStep`).
* `runSemijoin E Rel program` — a full pass, folding an arbitrary
  program `List (Fin m × Fin m)` of ordered semijoin instructions.
  Solution-set preservation (`runSemijoin_iInter`), monotone shrinkage
  (`runSemijoin_subset`) and support preservation
  (`runSemijoin_hasSupport`) hold for every program.
* Fixed point: `SemijoinStable E Rel` (no step shrinks anything) is
  *equivalent* to `PairwiseConsistent` of `Ste.AcyclicSolvability`
  specialized to full domains `D = fun _ => Set.univ`
  (`semijoinStable_iff_pairwiseConsistent`).  The specialization is the
  honest bridge: extensional tables carry no separate domain structure,
  and `PairwiseConsistent`'s domain-respecting quantification collapses
  to plain tuple quantification at `D u = univ`.
* Termination, in the repo's counting style (`Ste.Elimination`,
  `Ste.BucketConsistency`): over a finite alphabet a strictly shrinking
  step drops the total row count `∑ k, (Rel k).ncard` by at least one
  (`sum_ncard_semijoinStep_lt`), so *some* program of length at most
  `∑ k, (Rel k).ncard` reaches a stable state
  (`exists_stable_program`).  The existence form is chosen — matching
  the repo's honest style — rather than an executable
  iterate-until-stable function.
* Headline (`yannakakis_semijoin_guarantee`): on a GYO-reducible,
  edge-supported instance over a finite nonempty alphabet, there is a
  semijoin program of length at most the total initial row count whose
  run is stable, preserves the joint solution set exactly
  (`⋂ k, Rel' k = ⋂ k, Rel k`), and — whenever the stabilized tables
  are all nonempty — certifies that this common solution set is
  nonempty.  This is the full mechanized Yannakakis-style guarantee:
  a semijoin pass on an acyclic scheme decides joint satisfiability
  and loses no solutions.

Honest boundary.  (1) Complexity is operation-counted only: the bound
is on the *number of semijoin instructions*, not on a RAM-model running
time of executing one semijoin; per-instruction cost is bounded
separately by the table machinery of `Ste.Treewidth`
(`table_encard_le`).  (2) No optimality of program length is claimed —
Yannakakis's two-sweep program along a join tree uses `O(m)` semijoins,
while the bound here is the generic `∑ k, |Rel k|` of the naive
fair iteration; only existence within that bound is proved.  (3) The
existence form is proved rather than an executable well-founded
iterate; the extracted program depends on the instance.  (4) The
equivalence `SemijoinStable ↔ PairwiseConsistent` is stated at full
domains `D = fun _ => Set.univ`; for restricted domains one first
intersects the domains into the tables, which is a (unit) semijoin
against unary relations and is not separately modelled.

There is no `sorry` in this file: every statement made is proved.

References: M. Yannakakis, *Algorithms for acyclic database schemes*,
VLDB 1981, 82–94 (`yannakakis1981algorithms`); C. Beeri, R. Fagin,
D. Maier, M. Yannakakis, *On the desirability of acyclic database
schemes*, JACM 30(3):479–513, 1983 (`beeri1983acyclic`).
-/
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Ste.Support
import Ste.AcyclicSolvability

namespace STE

open Set

variable {α : Type*} {m n : ℕ}

/-! ### The one-step semijoin reduction -/

/-- **The semijoin** `Rel k ⋉ Rel k'`: the tuples of `Rel k` that match
some tuple of `Rel k'` on the shared attributes `E k ∩ E k'`.  This is
the set the one-step reduction replaces `Rel k` with. -/
def semijoinReduced (E : Fin m → Finset (Fin (n + 1)))
    (Rel : Fin m → Set (Fin (n + 1) → α)) (k k' : Fin m) :
    Set (Fin (n + 1) → α) :=
  {g ∈ Rel k | ∃ g' ∈ Rel k', ∀ u ∈ E k ∩ E k', g' u = g u}

theorem mem_semijoinReduced {E : Fin m → Finset (Fin (n + 1))}
    {Rel : Fin m → Set (Fin (n + 1) → α)} {k k' : Fin m}
    {g : Fin (n + 1) → α} :
    g ∈ semijoinReduced E Rel k k' ↔
      g ∈ Rel k ∧ ∃ g' ∈ Rel k', ∀ u ∈ E k ∩ E k', g' u = g u :=
  Iff.rfl

/-- A semijoin only removes tuples. -/
theorem semijoinReduced_subset (E : Fin m → Finset (Fin (n + 1)))
    (Rel : Fin m → Set (Fin (n + 1) → α)) (k k' : Fin m) :
    semijoinReduced E Rel k k' ⊆ Rel k :=
  fun _ h => h.1

/-- **The one-step semijoin reduce** of edge `k` by edge `k'`: table
`k` is replaced by the semijoin `Rel k ⋉ Rel k'`; every other table is
untouched. -/
def semijoinStep (E : Fin m → Finset (Fin (n + 1)))
    (Rel : Fin m → Set (Fin (n + 1) → α)) (k k' : Fin m) :
    Fin m → Set (Fin (n + 1) → α) :=
  Function.update Rel k (semijoinReduced E Rel k k')

@[simp] theorem semijoinStep_self (E : Fin m → Finset (Fin (n + 1)))
    (Rel : Fin m → Set (Fin (n + 1) → α)) (k k' : Fin m) :
    semijoinStep E Rel k k' k = semijoinReduced E Rel k k' :=
  Function.update_self ..

theorem semijoinStep_of_ne (E : Fin m → Finset (Fin (n + 1)))
    (Rel : Fin m → Set (Fin (n + 1) → α)) (k k' : Fin m) {j : Fin m}
    (h : j ≠ k) : semijoinStep E Rel k k' j = Rel j :=
  Function.update_of_ne h ..

/-- **(a) Monotone shrinkage**: a step shrinks only `Rel k`, and only
downward — pointwise `⊆` at every index. -/
theorem semijoinStep_subset (E : Fin m → Finset (Fin (n + 1)))
    (Rel : Fin m → Set (Fin (n + 1) → α)) (k k' : Fin m) (j : Fin m) :
    semijoinStep E Rel k k' j ⊆ Rel j := by
  rcases eq_or_ne j k with rfl | h
  · rw [semijoinStep_self]
    exact semijoinReduced_subset E Rel j k'
  · rw [semijoinStep_of_ne E Rel k k' h]

/-- **(b) Solution-set preservation**: a semijoin step does not change
the joint solution set — a tuple removed from `Rel k` matches no tuple
of `Rel k'` even on the shared attributes, so it extends to no global
solution. -/
theorem semijoinStep_iInter (E : Fin m → Finset (Fin (n + 1)))
    (Rel : Fin m → Set (Fin (n + 1) → α)) (k k' : Fin m) :
    ⋂ j, semijoinStep E Rel k k' j = ⋂ j, Rel j := by
  refine Set.Subset.antisymm
    (Set.iInter_mono fun j => semijoinStep_subset E Rel k k' j) ?_
  intro g hg
  simp only [Set.mem_iInter] at hg ⊢
  intro j
  rcases eq_or_ne j k with rfl | h
  · rw [semijoinStep_self]
    exact ⟨hg j, g, hg k', fun u _ => rfl⟩
  · rw [semijoinStep_of_ne E Rel k k' h]
    exact hg j

/-- The semijoin of a `E k`-supported table remains `E k`-supported:
membership reads `g` only on `E k`, and the matching condition reads it
only on `E k ∩ E k' ⊆ E k`. -/
theorem hasSupport_semijoinReduced (E : Fin m → Finset (Fin (n + 1)))
    (Rel : Fin m → Set (Fin (n + 1) → α)) {k : Fin m} (k' : Fin m)
    (hk : HasSupport (Rel k) ↑(E k)) :
    HasSupport (semijoinReduced E Rel k k') ↑(E k) := by
  intro f g hfg
  have hEk : ∀ u ∈ E k ∩ E k', f u = g u := fun u hu =>
    hfg u (Finset.mem_coe.mpr (Finset.mem_inter.mp hu).1)
  simp only [mem_semijoinReduced]
  refine and_congr (hk f g hfg) ⟨?_, ?_⟩
  · rintro ⟨g', hg', ha⟩
    exact ⟨g', hg', fun u hu => (ha u hu).trans (hEk u hu)⟩
  · rintro ⟨g', hg', ha⟩
    exact ⟨g', hg', fun u hu => (ha u hu).trans (hEk u hu).symm⟩

/-- **(c) Support preservation**: a semijoin step preserves the scope
of every table. -/
theorem hasSupport_semijoinStep (E : Fin m → Finset (Fin (n + 1)))
    (Rel : Fin m → Set (Fin (n + 1) → α)) (k k' : Fin m)
    (hsupp : ∀ j, HasSupport (Rel j) ↑(E j)) (j : Fin m) :
    HasSupport (semijoinStep E Rel k k' j) ↑(E j) := by
  rcases eq_or_ne j k with rfl | h
  · rw [semijoinStep_self]
    exact hasSupport_semijoinReduced E Rel k' (hsupp j)
  · rw [semijoinStep_of_ne E Rel k k' h]
    exact hsupp j

/-! ### A full semijoin program -/

/-- **Running a semijoin program**: fold the ordered instructions
`(k, k')` — "reduce table `k` by table `k'`" — over the tables, left to
right. -/
def runSemijoin (E : Fin m → Finset (Fin (n + 1))) :
    (Fin m → Set (Fin (n + 1) → α)) → List (Fin m × Fin m) →
      Fin m → Set (Fin (n + 1) → α)
  | Rel, [] => Rel
  | Rel, p :: ps => runSemijoin E (semijoinStep E Rel p.1 p.2) ps

@[simp] theorem runSemijoin_nil (E : Fin m → Finset (Fin (n + 1)))
    (Rel : Fin m → Set (Fin (n + 1) → α)) :
    runSemijoin E Rel [] = Rel := rfl

@[simp] theorem runSemijoin_cons (E : Fin m → Finset (Fin (n + 1)))
    (Rel : Fin m → Set (Fin (n + 1) → α)) (p : Fin m × Fin m)
    (ps : List (Fin m × Fin m)) :
    runSemijoin E Rel (p :: ps)
      = runSemijoin E (semijoinStep E Rel p.1 p.2) ps := rfl

/-- **Monotone shrinkage for programs**: every program only removes
tuples, at every index. -/
theorem runSemijoin_subset (E : Fin m → Finset (Fin (n + 1)))
    (program : List (Fin m × Fin m)) :
    ∀ (Rel : Fin m → Set (Fin (n + 1) → α)) (j : Fin m),
      runSemijoin E Rel program j ⊆ Rel j := by
  induction program with
  | nil => intro Rel j; exact subset_rfl
  | cons p ps ih =>
      intro Rel j
      exact (ih (semijoinStep E Rel p.1 p.2) j).trans
        (semijoinStep_subset E Rel p.1 p.2 j)

/-- **Solution-set preservation for programs**: no semijoin program
changes the joint solution set. -/
theorem runSemijoin_iInter (E : Fin m → Finset (Fin (n + 1)))
    (program : List (Fin m × Fin m)) :
    ∀ Rel : Fin m → Set (Fin (n + 1) → α),
      ⋂ j, runSemijoin E Rel program j = ⋂ j, Rel j := by
  induction program with
  | nil => intro Rel; rfl
  | cons p ps ih =>
      intro Rel
      rw [runSemijoin_cons, ih (semijoinStep E Rel p.1 p.2),
        semijoinStep_iInter]

/-- **Support preservation for programs**. -/
theorem runSemijoin_hasSupport (E : Fin m → Finset (Fin (n + 1)))
    (program : List (Fin m × Fin m)) :
    ∀ Rel : Fin m → Set (Fin (n + 1) → α),
      (∀ j, HasSupport (Rel j) ↑(E j)) →
      ∀ j, HasSupport (runSemijoin E Rel program j) ↑(E j) := by
  induction program with
  | nil => intro Rel hsupp j; exact hsupp j
  | cons p ps ih =>
      intro Rel hsupp j
      exact ih (semijoinStep E Rel p.1 p.2)
        (hasSupport_semijoinStep E Rel p.1 p.2 hsupp) j

/-! ### The fixed point: stability = pairwise consistency -/

/-- **Semijoin stability**: no semijoin step removes any tuple — every
instruction is a no-op.  This is the fixed point of the reduction
process. -/
def SemijoinStable (E : Fin m → Finset (Fin (n + 1)))
    (Rel : Fin m → Set (Fin (n + 1) → α)) : Prop :=
  ∀ k k' : Fin m, semijoinReduced E Rel k k' = Rel k

/-- **The fixed-point characterization**: semijoin stability is exactly
`PairwiseConsistent` of `Ste.AcyclicSolvability`, specialized to the
full domains `D = fun _ => Set.univ` and to the propositional reading
`fun k g => g ∈ Rel k` of the tables.  (Extensional tables carry no
separate domain structure; at `D u = univ` the domain-respecting
quantification of `PairwiseConsistent` collapses to plain tuple
quantification, which is precisely "every tuple of `Rel k` survives
every semijoin".) -/
theorem semijoinStable_iff_pairwiseConsistent
    (E : Fin m → Finset (Fin (n + 1)))
    (Rel : Fin m → Set (Fin (n + 1) → α)) :
    SemijoinStable E Rel ↔
      PairwiseConsistent (fun _ => (Set.univ : Set α)) E
        (fun k g => g ∈ Rel k) := by
  constructor
  · intro h k k' g _ hgk
    have hgred : g ∈ semijoinReduced E Rel k k' := (h k k').symm ▸ hgk
    obtain ⟨-, g', hg', ha⟩ := mem_semijoinReduced.mp hgred
    exact ⟨g', fun u => Set.mem_univ _, hg', ha⟩
  · intro h k k'
    refine Set.Subset.antisymm (semijoinReduced_subset E Rel k k') ?_
    intro g hg
    obtain ⟨g', -, hg'k', ha⟩ := h k k' g (fun u => Set.mem_univ _) hg
    exact ⟨hg, g', hg'k', ha⟩

/-- The `HasSupport` reading of the tables is the `EdgeSupported`
hypothesis of `Ste.AcyclicSolvability`. -/
theorem edgeSupported_of_hasSupport (E : Fin m → Finset (Fin (n + 1)))
    (Rel : Fin m → Set (Fin (n + 1) → α))
    (hsupp : ∀ k, HasSupport (Rel k) ↑(E k)) :
    EdgeSupported E fun k g => g ∈ Rel k :=
  fun k g g' ha => hsupp k g g' fun u hu => ha u (Finset.mem_coe.mp hu)

/-- **Stable nonempty tables on an acyclic scheme have a common
solution.**  The composition of the fixed-point characterization with
`gyoReducible_pairwiseConsistent_solvable`: on a GYO-reducible
hypergraph, semijoin-stable nonempty edge-supported tables intersect. -/
theorem semijoinStable_solvable [Nonempty α]
    {E : Fin m → Finset (Fin (n + 1))}
    {Rel : Fin m → Set (Fin (n + 1) → α)}
    (hgyo : GYOReducible E) (hsupp : ∀ k, HasSupport (Rel k) ↑(E k))
    (hstab : SemijoinStable E Rel) (hne : ∀ k, (Rel k).Nonempty) :
    (⋂ k, Rel k).Nonempty := by
  obtain ⟨f, -, hf⟩ := gyoReducible_pairwiseConsistent_solvable hgyo
    (edgeSupported_of_hasSupport E Rel hsupp)
    ((semijoinStable_iff_pairwiseConsistent E Rel).mp hstab)
    (fun k => Exists.imp (fun t ht => ⟨fun u => Set.mem_univ _, ht⟩) (hne k))
    (fun _ => Set.univ_nonempty)
  exact ⟨f, Set.mem_iInter.mpr hf⟩

/-! ### Termination: the total row count is a strictly decreasing measure -/

/-- **The counting step** (repo counting style, cf.
`Ste.Elimination.elimination_order_table_total_bound`): over a finite
alphabet, a semijoin step that actually removes something strictly
decreases the total row count `∑ k, (Rel k).ncard` — each strict step
removes at least one tuple from exactly one table. -/
theorem sum_ncard_semijoinStep_lt [Finite α]
    (E : Fin m → Finset (Fin (n + 1)))
    (Rel : Fin m → Set (Fin (n + 1) → α)) {k k' : Fin m}
    (h : semijoinReduced E Rel k k' ≠ Rel k) :
    ∑ j, (semijoinStep E Rel k k' j).ncard < ∑ j, (Rel j).ncard := by
  refine Finset.sum_lt_sum (fun j _ => ?_) ⟨k, Finset.mem_univ k, ?_⟩
  · exact Set.ncard_le_ncard (semijoinStep_subset E Rel k k' j)
      (Set.toFinite _)
  · rw [semijoinStep_self]
    exact Set.ncard_lt_ncard
      ((semijoinReduced_subset E Rel k k').ssubset_of_ne h)
      (Set.toFinite _)

/-- **Termination / complexity, existence form**: over a finite
alphabet there is a semijoin program of length at most the total
initial row count `∑ k, (Rel k).ncard` whose run is semijoin-stable.
(The program is the greedy one: as long as some instruction strictly
shrinks, execute it; `sum_ncard_semijoinStep_lt` caps the number of
strict steps.  This is the operation-count bound of the naive fair
iteration; Yannakakis's `O(m)`-semijoin program along a join tree is
not claimed.) -/
theorem exists_stable_program [Finite α]
    (E : Fin m → Finset (Fin (n + 1)))
    (Rel : Fin m → Set (Fin (n + 1) → α)) :
    ∃ program : List (Fin m × Fin m),
      program.length ≤ ∑ k, (Rel k).ncard ∧
      SemijoinStable E (runSemijoin E Rel program) := by
  suffices h : ∀ (N : ℕ) (Rel : Fin m → Set (Fin (n + 1) → α)),
      ∑ k, (Rel k).ncard ≤ N →
      ∃ program : List (Fin m × Fin m), program.length ≤ N ∧
        SemijoinStable E (runSemijoin E Rel program) from
    h (∑ k, (Rel k).ncard) Rel le_rfl
  intro N
  induction N with
  | zero =>
      intro Rel hN
      by_cases hstab : SemijoinStable E Rel
      · exact ⟨[], le_rfl, hstab⟩
      · exfalso
        simp only [SemijoinStable, not_forall] at hstab
        obtain ⟨k, k', hne⟩ := hstab
        have hlt := sum_ncard_semijoinStep_lt E Rel hne
        omega
  | succ N ih =>
      intro Rel hN
      by_cases hstab : SemijoinStable E Rel
      · exact ⟨[], Nat.zero_le _, hstab⟩
      · simp only [SemijoinStable, not_forall] at hstab
        obtain ⟨k, k', hne⟩ := hstab
        have hlt := sum_ncard_semijoinStep_lt E Rel hne
        obtain ⟨program, hlen, hstab'⟩ :=
          ih (semijoinStep E Rel k k') (by omega)
        refine ⟨(k, k') :: program, ?_, hstab'⟩
        rw [List.length_cons]
        omega

/-! ### The headline: the mechanized Yannakakis guarantee -/

/-- **The Yannakakis-style semijoin guarantee, fully composed**
(`yannakakis1981algorithms`, `beeri1983acyclic`): on a GYO-reducible
(α-acyclic) hypergraph with edge-supported tables over a finite
nonempty alphabet, there is a semijoin program, of length at most the
total initial row count, whose run

1. is semijoin-stable (pairwise-consistent, by
   `semijoinStable_iff_pairwiseConsistent`),
2. preserves the joint solution set *exactly* —
   `⋂ k, Rel' k = ⋂ k, Rel k`, no solution is lost and none is added,
3. only shrinks the tables, preserving their scopes, and
4. decides joint satisfiability: if the stabilized tables are all
   nonempty then the (original) joint solution set is nonempty.

Contrapositively, if any stabilized table is empty then so is the
joint solution set (by 2 and monotone shrinkage) — the semijoin pass
is a sound and complete satisfiability test on acyclic schemes. -/
theorem yannakakis_semijoin_guarantee [Nonempty α] [Finite α]
    {E : Fin m → Finset (Fin (n + 1))}
    {Rel : Fin m → Set (Fin (n + 1) → α)}
    (hgyo : GYOReducible E) (hsupp : ∀ k, HasSupport (Rel k) ↑(E k)) :
    ∃ program : List (Fin m × Fin m),
      program.length ≤ ∑ k, (Rel k).ncard ∧
      SemijoinStable E (runSemijoin E Rel program) ∧
      (⋂ k, runSemijoin E Rel program k) = ⋂ k, Rel k ∧
      (∀ k, runSemijoin E Rel program k ⊆ Rel k) ∧
      ((∀ k, (runSemijoin E Rel program k).Nonempty) →
        (⋂ k, Rel k).Nonempty) := by
  obtain ⟨program, hlen, hstab⟩ := exists_stable_program E Rel
  refine ⟨program, hlen, hstab, runSemijoin_iInter E program Rel,
    runSemijoin_subset E program Rel, fun hne => ?_⟩
  rw [← runSemijoin_iInter E program Rel]
  exact semijoinStable_solvable hgyo
    (runSemijoin_hasSupport E program Rel hsupp) hstab hne

end STE
