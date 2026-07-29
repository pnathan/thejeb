/-
Fuzzy (graded, `[0,1]`-valued) STE frames.

Combettes 1993, §II-C specifies each piece of information by a property set
`Sᵢ = {a ∈ Ξ | Ψᵢ(a) ≥ ψᵢ}` (Eq. (3)) cut from a real-valued satisfaction
function `Ψᵢ`.  `Ste.Basic` mechanizes the crisp case where `Ψᵢ` is
`{0,1}`-valued, and explicitly names the graded generalization -- `Ψᵢ : Ξ →
[0,1]` -- as future work.  This module discharges that: `Ξ`'s crisp property
sets are replaced by *possibility distributions* `μ : Ξ → [0,1]` (Zadeh,
"Fuzzy Sets," Information and Control 8:338-353, 1965; Zadeh, "Fuzzy sets as
a basis for a theory of possibility," Fuzzy Sets and Systems 1:3-28, 1978),
combined by the min t-norm (the largest, and the unique idempotent, t-norm:
Klement, Mesiar, Pap, *Triangular Norms*, Kluwer, 2000).  Every crisp
Combettes construction -- property set, feasibility set, information
monotonicity, and (Tier 3) the frame-corpus Helly-2 theorem of
`Ste.HellyConsistency` -- has a graded analogue here, and each graded
statement degrades to exactly its crisp counterpart at the `{0,1}` boundary
or under an `α`-cut (Zadeh's level-set device).  Tier 3's confidence-weighted
corpus is a *certainty-qualified* frame in the sense of Dubois & Prade,
*Possibility Theory* (Plenum, 1988): an author with confidence `conf a`
imposes the possibility distribution `π = max(χ_{S_a}, 1 - conf a)`, so that
doubting the author (low confidence) only ever raises possibility, never
lowers it.

Main results:
* `FuzzyFrame.crisp_inter` / `crisp_pinter` (degradation law 1): on the
  `{0,1}` boundary, the min and product t-norms coincide with ordinary
  intersection, so the choice of t-norm is invisible on crisp data.
* `fuzzyFeasibility_crisp` (degradation law 2): the min-combined graded
  feasibility of a family of crisp frames is exactly the crisp frame of the
  Combettes feasibility set.
* `le_consistencyDegree_iff` (the resolution identity): graded consistency
  at level `α` is exactly crisp Combettes consistency of the `α`-cut corpus,
  transferring every crisp result level-by-level.
* `weightedFrame_gradedHelly_two`: the graded analogue of
  `Ste.HellyConsistency.frame_hasHelly_two` for confidence-weighted frame
  corpora -- pairwise joint possibility at level `α` forces global joint
  possibility at level `α`, for any confidence weighting.

Reference: P. L. Combettes, "The Foundations of Set Theoretic Estimation,"
Proc. IEEE 81(2), 1993, §II-C.
-/
import Ste.Basic
import Ste.FiniteInstance
import Ste.HellyConsistency
import Mathlib.Topology.UnitInterval

namespace STE

noncomputable section

open scoped Classical

/-! ### Tier 1: the graded frame and its crisp boundary -/

/-- A graded Combettes property set / Zadeh possibility distribution on `Ξ`:
`μ a` is the degree, in `[0,1]`, to which hypothesis `a` is compatible with a
piece of evidence (Zadeh 1965; Zadeh 1978's possibility distributions).  The
crisp property sets of `Ste.Basic` are the `{0,1}`-valued members
(`FuzzyFrame.crisp`, `FuzzyFrame.IsCrisp`) -- this is precisely the graded
generalization `Ste.Basic`'s header names as future work. -/
def FuzzyFrame (Ξ : Type*) := Ξ → unitInterval

variable {Ξ : Type*}

/-- The `{0,1}`-embedding of a crisp property set `S`: full membership (`1`)
inside `S`, none (`0`) outside. -/
def FuzzyFrame.crisp (S : Set Ξ) : FuzzyFrame Ξ := fun a => if a ∈ S then 1 else 0

/-- A graded frame is *crisp* when it only ever takes the boundary values `0`
and `1`, i.e. it is (up to `crisp`) an ordinary Combettes property set. -/
def FuzzyFrame.IsCrisp (μ : FuzzyFrame Ξ) : Prop := ∀ a, μ a = 0 ∨ μ a = 1

/-- The embedding of a crisp set is itself crisp. -/
theorem FuzzyFrame.isCrisp_crisp (S : Set Ξ) : (FuzzyFrame.crisp S).IsCrisp := by
  intro a
  by_cases h : a ∈ S <;> simp [FuzzyFrame.crisp, h]

/-- Min-t-norm intersection: the pointwise lattice meet of two graded
frames, Zadeh's (1965) original fuzzy intersection. -/
def FuzzyFrame.inter (μ ν : FuzzyFrame Ξ) : FuzzyFrame Ξ := fun a => μ a ⊓ ν a

/-- Product-t-norm intersection: an alternative, non-idempotent combination
rule.  Included only to exhibit `crisp_pinter`: the choice of t-norm is
invisible on crisp data, since `min` and `·` agree on `{0,1}` (Klement,
Mesiar, Pap 2000: `min` is the largest, and the unique idempotent, t-norm). -/
def FuzzyFrame.pinter (μ ν : FuzzyFrame Ξ) : FuzzyFrame Ξ := fun a => μ a * ν a

/-- **Degradation law 1 (min t-norm).** The min-t-norm intersection of two
crisp frames is the crisp embedding of their set intersection: on the
`{0,1}` boundary, `⊓` recovers ordinary set intersection. -/
theorem FuzzyFrame.crisp_inter (S T : Set Ξ) :
    (FuzzyFrame.crisp S).inter (FuzzyFrame.crisp T) = FuzzyFrame.crisp (S ∩ T) := by
  funext a
  by_cases hS : a ∈ S <;> by_cases hT : a ∈ T <;>
    simp [FuzzyFrame.inter, FuzzyFrame.crisp, hS, hT]

/-- **Degradation law 1 (product t-norm).** The product-t-norm intersection
of two crisp frames also recovers ordinary set intersection: the two t-norms
agree at the crisp boundary, so the choice between them is invisible there. -/
theorem FuzzyFrame.crisp_pinter (S T : Set Ξ) :
    (FuzzyFrame.crisp S).pinter (FuzzyFrame.crisp T) = FuzzyFrame.crisp (S ∩ T) := by
  funext a
  by_cases hS : a ∈ S <;> by_cases hT : a ∈ T <;>
    simp [FuzzyFrame.pinter, FuzzyFrame.crisp, hS, hT]

/-- The `α`-cut of a graded frame: the crisp set of hypotheses whose
compatibility degree reaches at least `α`.  Zadeh's level-set device, the
standard tool for transferring crisp results to the graded case. -/
def FuzzyFrame.cut (α : unitInterval) (μ : FuzzyFrame Ξ) : Set Ξ := {a | α ≤ μ a}

/-- Cuts commute with the min-t-norm intersection: an `α`-cut of a meet is
the intersection of the `α`-cuts. -/
theorem FuzzyFrame.cut_inter (α : unitInterval) (μ ν : FuzzyFrame Ξ) :
    FuzzyFrame.cut α (μ.inter ν) = FuzzyFrame.cut α μ ∩ FuzzyFrame.cut α ν := by
  ext a
  simp [FuzzyFrame.cut, FuzzyFrame.inter, le_inf_iff]

/-- Any positive-level cut of a crisp frame recovers the original set. -/
theorem FuzzyFrame.cut_crisp {S : Set Ξ} {α : unitInterval} (h : 0 < α) :
    FuzzyFrame.cut α (FuzzyFrame.crisp S) = S := by
  ext a
  by_cases ha : a ∈ S <;>
    simp [FuzzyFrame.cut, FuzzyFrame.crisp, ha, h.ne', unitInterval.le_one']

/-- Cuts are antitone in the level: a higher bar for compatibility cuts out
a smaller (or equal) set of hypotheses. -/
theorem FuzzyFrame.cut_antitone {μ : FuzzyFrame Ξ} {α β : unitInterval} (h : α ≤ β) :
    FuzzyFrame.cut β μ ⊆ FuzzyFrame.cut α μ :=
  fun _ ha => h.trans ha

/-! ### Tier 2: corpora, graded feasibility, the resolution identity -/

variable {ι : Type*}

/-- The graded feasibility frame of a corpus `S : ι → FuzzyFrame Ξ`: the
min-t-norm combination of every constraint, i.e. the pointwise infimum of
all pieces of graded evidence.  An empty corpus gives the everywhere-`1`
frame (the `Finset.univ = ∅` case of `Finset.inf`, via `OrderTop`), matching
`feasibilitySet` of an empty family being `Set.univ`. -/
def fuzzyFeasibility [Fintype ι] (S : ι → FuzzyFrame Ξ) : FuzzyFrame Ξ :=
  fun a => Finset.univ.inf (fun i => S i a)

/-- **Degradation law 2 (the headline of Tier 2).** Min-combining a family
of crisp frames is exactly the crisp embedding of the Combettes feasibility
set (`Ste.Basic`) of the underlying crisp property sets. -/
theorem fuzzyFeasibility_crisp [Fintype ι] (S : ι → Set Ξ) :
    fuzzyFeasibility (fun i => FuzzyFrame.crisp (S i)) = FuzzyFrame.crisp (feasibilitySet S) := by
  funext a
  show Finset.univ.inf (fun i => FuzzyFrame.crisp (S i) a) = FuzzyFrame.crisp (feasibilitySet S) a
  by_cases ha : a ∈ feasibilitySet S
  · have hall : ∀ i, a ∈ S i := mem_feasibilitySet.mp ha
    have hconst : (fun i => FuzzyFrame.crisp (S i) a) = fun _ : ι => (1 : unitInterval) :=
      funext fun i => if_pos (hall i)
    rw [hconst, FuzzyFrame.crisp, if_pos ha]
    refine le_antisymm le_top ?_
    rw [Finset.le_inf_iff]
    exact fun i _ => le_top
  · have hnall : ¬ ∀ i, a ∈ S i := fun h => ha (mem_feasibilitySet.mpr h)
    obtain ⟨i, hi⟩ := not_forall.mp hnall
    have hzero : FuzzyFrame.crisp (S i) a = 0 := if_neg hi
    have hle : Finset.univ.inf (fun i => FuzzyFrame.crisp (S i) a) ≤ 0 :=
      hzero ▸ Finset.inf_le (Finset.mem_univ i)
    rw [FuzzyFrame.crisp, if_neg ha]
    exact le_antisymm hle bot_le

/-- **Cut commutation for corpora.** The `α`-cut of a graded feasibility
frame is the Combettes feasibility set of the `α`-cut corpus, for every
level `α` (the hypothesis-free direction: `Finset.le_inf_iff` needs no
positivity assumption on `α`). -/
theorem cut_fuzzyFeasibility [Fintype ι] (α : unitInterval) (S : ι → FuzzyFrame Ξ) :
    FuzzyFrame.cut α (fuzzyFeasibility S) = feasibilitySet (fun i => FuzzyFrame.cut α (S i)) := by
  ext a
  simp [FuzzyFrame.cut, fuzzyFeasibility, mem_feasibilitySet, Finset.le_inf_iff]

/-- The graded partial feasibility frame: only the constraints indexed by
the finite set `J` are enforced.  The graded analogue of
`Ste.Basic.partialFeasibilitySet`. -/
def fuzzyPartialFeasibility (S : ι → FuzzyFrame Ξ) (J : Finset ι) : FuzzyFrame Ξ :=
  fun a => J.inf (fun i => S i a)

/-- **Graded information monotonicity.** Enforcing more constraints can only
lower (never raise) possibility -- the graded analogue of
`Ste.Basic.partialFeasibilitySet_antitone`: there, acquiring more information
shrinks the feasibility set; here, acquiring more information shrinks each
hypothesis's compatibility degree. -/
theorem fuzzyPartialFeasibility_antitone (S : ι → FuzzyFrame Ξ) {J K : Finset ι}
    (hJK : J ⊆ K) (a : Ξ) :
    fuzzyPartialFeasibility S K a ≤ fuzzyPartialFeasibility S J a :=
  Finset.inf_mono hJK

/-- The **height** of a graded frame on a finite hypothesis space: the
largest degree of compatibility attained by any hypothesis, i.e. how
consistent the frame is with *some* candidate. -/
def FuzzyFrame.height [Fintype Ξ] (μ : FuzzyFrame Ξ) : unitInterval := Finset.univ.sup μ

/-- The **consistency degree** of a graded corpus: the height of its graded
feasibility frame, i.e. the highest level `α` at which some hypothesis is
compatible with every piece of evidence to degree at least `α`. -/
def consistencyDegree [Fintype Ξ] [Fintype ι] (S : ι → FuzzyFrame Ξ) : unitInterval :=
  (fuzzyFeasibility S).height

/-- **The resolution identity (the bridge theorem, Zadeh 1971/1978 style).**
Graded consistency at a positive level `α` is *exactly* crisp Combettes
consistency (`Ste.Basic`) of the `α`-cut corpus.  This is the theorem that
transfers every crisp STE result level-by-level to the graded setting. -/
theorem le_consistencyDegree_iff [Fintype Ξ] [Fintype ι] {α : unitInterval} (hα : 0 < α)
    (S : ι → FuzzyFrame Ξ) :
    α ≤ consistencyDegree S ↔ (feasibilitySet (fun i => FuzzyFrame.cut α (S i))).Nonempty := by
  have hcut : ∀ a, a ∈ feasibilitySet (fun i => FuzzyFrame.cut α (S i)) ↔
      α ≤ fuzzyFeasibility S a := by
    intro a
    rw [← cut_fuzzyFeasibility]
    simp [FuzzyFrame.cut]
  unfold consistencyDegree FuzzyFrame.height
  rw [Finset.le_sup_iff hα]
  constructor
  · rintro ⟨a, -, ha⟩
    exact ⟨a, (hcut a).mpr ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Finset.mem_univ a, (hcut a).mp ha⟩

/-- **Degenerate degradation corollary.** A confidence-free family of crisp
frames has consistency degree exactly `1` iff the underlying Combettes
corpus is consistent -- the `α = 1` instance of the resolution identity. -/
theorem consistencyDegree_crisp_eq_one_iff [Fintype Ξ] [Fintype ι] (S : ι → Set Ξ) :
    consistencyDegree (fun i => FuzzyFrame.crisp (S i)) = 1 ↔ (feasibilitySet S).Nonempty := by
  have hcut : (fun i => FuzzyFrame.cut (1 : unitInterval) (FuzzyFrame.crisp (S i))) = S :=
    funext fun i => FuzzyFrame.cut_crisp zero_lt_one
  constructor
  · intro h
    have h1 : (1 : unitInterval) ≤ consistencyDegree (fun i => FuzzyFrame.crisp (S i)) :=
      le_of_eq h.symm
    have := (le_consistencyDegree_iff zero_lt_one _).mp h1
    rwa [hcut] at this
  · intro h
    have h' : (feasibilitySet (fun i => FuzzyFrame.cut (1 : unitInterval)
        (FuzzyFrame.crisp (S i)))).Nonempty := by rwa [hcut]
    have hle : (1 : unitInterval) ≤ consistencyDegree (fun i => FuzzyFrame.crisp (S i)) :=
      (le_consistencyDegree_iff zero_lt_one _).mpr h'
    exact le_antisymm unitInterval.le_one' hle

/-! ### Tier 3: graded Helly-2 for confidence-weighted frame corpora -/

variable {A V W : Type*}

/-- **Certainty-qualified frame constraint.** An author `a` with confidence
`conf a` imposes the possibility distribution `π = max(χ_{S_a}, 1 - conf a)`
(Dubois & Prade 1988: certainty-qualified statements "`N(S_a) ≥ conf a`"):
full possibility (`1`) for assignments consistent with the author's crisp
frame, and residual possibility `1 - conf a` (the author's *doubt*) for
everything else.  Confidence `1` imposes the crisp frame outright;
confidence `0` imposes nothing at all (every assignment gets possibility
`1`). -/
def weightedFrameConstraint (frame : A → V → Option W) (conf : A → unitInterval)
    (a : A) : FuzzyFrame (V → W) :=
  fun f => if f ∈ frameConstraint frame a then 1 else unitInterval.symm (conf a)

/-- The thresholded (crisp) corpus at level `α`: authors whose doubt
`1 - conf a` already reaches `α` are erased (their assertion is replaced by
total silence), since at level `α` their residual possibility everywhere
already dominates the bar. -/
def thresholdFrame (frame : A → V → Option W) (conf : A → unitInterval)
    (α : unitInterval) : A → V → Option W :=
  fun a => if α ≤ unitInterval.symm (conf a) then (fun _ => none) else frame a

/-- **The cut lemma.** The `α`-cut of a certainty-qualified frame constraint
is exactly the crisp frame constraint of the thresholded corpus: erased
(silent) authors contribute the whole space at every level, and surviving
authors contribute their original crisp frame unchanged. -/
theorem cut_weightedFrameConstraint (frame : A → V → Option W) (conf : A → unitInterval)
    (α : unitInterval) (a : A) :
    FuzzyFrame.cut α (weightedFrameConstraint frame conf a)
      = frameConstraint (thresholdFrame frame conf α) a := by
  by_cases hα : α ≤ unitInterval.symm (conf a)
  · have hthresh : thresholdFrame frame conf α a = fun _ => none := if_pos hα
    have hRHS : frameConstraint (thresholdFrame frame conf α) a = Set.univ := by
      apply Set.eq_univ_of_forall
      intro f v x hx
      rw [hthresh] at hx
      simp at hx
    rw [hRHS]
    apply Set.eq_univ_of_forall
    intro f
    show α ≤ weightedFrameConstraint frame conf a f
    unfold weightedFrameConstraint
    split_ifs with hf
    · exact unitInterval.le_one'
    · exact hα
  · have hthresh : thresholdFrame frame conf α a = frame a := if_neg hα
    have hRHS : frameConstraint (thresholdFrame frame conf α) a = frameConstraint frame a := by
      unfold frameConstraint
      rw [hthresh]
    rw [hRHS]
    ext f
    show (α ≤ weightedFrameConstraint frame conf a f) ↔ f ∈ frameConstraint frame a
    unfold weightedFrameConstraint
    split_ifs with hf
    · exact iff_of_true unitInterval.le_one' hf
    · exact iff_of_false hα hf

/-- **Graded Helly-2 (the crown result).** The graded analogue of
`Ste.HellyConsistency.frame_hasHelly_two`: for a confidence-weighted frame
corpus, if every PAIR of authors is jointly possible at level `α`, the WHOLE
corpus is jointly possible at level `α`.  Proof route: the cut lemma
(`cut_weightedFrameConstraint`) turns the `α`-cut family into the crisp
frame constraint of the thresholded corpus; `frame_hasHelly_two`
(`Ste.HellyConsistency`) certifies crisp global feasibility from pairwise
feasibility; the resolution identity (`le_consistencyDegree_iff`) lifts that
back to graded consistency at level `α`.  At `conf ≡ 1` (no author ever
doubted) and `α = 1`, this degrades to exactly `frame_hasHelly_two`. -/
theorem weightedFrame_gradedHelly_two [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] [Inhabited W]
    (frame : A → V → Option W) (conf : A → unitInterval)
    {α : unitInterval} (hα : 0 < α)
    (h2 : KWiseConsistent (fun a => FuzzyFrame.cut α (weightedFrameConstraint frame conf a)) 2) :
    α ≤ consistencyDegree (weightedFrameConstraint frame conf) := by
  have hrw : (fun a => FuzzyFrame.cut α (weightedFrameConstraint frame conf a))
      = frameConstraint (thresholdFrame frame conf α) :=
    funext (cut_weightedFrameConstraint frame conf α)
  apply (le_consistencyDegree_iff hα _).mpr
  rw [hrw]
  exact frame_hasHelly_two (thresholdFrame frame conf α) (hrw ▸ h2)

end

end STE
