/-
A **computable** refinement of the set-theoretic feasibility spec for the
finite, frame-structured case (Combettes 1993, mechanized in `Ste.Basic`).

The general STE spec has each piece of information `a` cut out a property
set `S a ⊆ Ξ` and asks whether `feasibilitySet S = ⋂ a, S a` is empty --
a `Set`-level (undecidable in general) question. Many empirical instances
have far more structure: each author fixes a *partial assignment* of
values to a finite set of variables (`frame a : V → Option W`, silence =
`none`), and the property set is the total assignments agreeing with it.

For that shape the feasibility question collapses to a **decidable,
pairwise** one: the corpus is jointly satisfiable iff no two authors ever
assign the *same variable* two *different values*. This module proves that
collapse -- `feasibilitySet_eq_empty_iff` ties the `Set`-level verdict of
`Ste.Basic` to the `by decide`-checkable predicate `Consistent` -- and
adds the quantitative `disagreementDegree` (how many distinct values a
variable receives), so a concrete corpus can have its invariants computed
by the Lean kernel rather than asserted.

The point is the *bridge*: `Consistent` and `disagreementDegree` are
computable, and they are proved equal to the verified `Set`-based
`feasibilitySet` spec, so nothing is trusted that the kernel has not
checked.

Reference: P. L. Combettes, "The Foundations of Set Theoretic
Estimation," Proc. IEEE 81(2), 1993.
-/
import Ste.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Option

namespace STE

variable {A V W : Type*}

/-- **The property set of a frame author.** Given `frame a : V → Option W`
(the value `a` fixes for each variable, `none` where silent), the total
assignments `f : V → W` agreeing with `a` wherever `a` speaks. This is the
general form of `Ste.TidesCorpus.constraint`. -/
def frameConstraint (frame : A → V → Option W) (a : A) : Set (V → W) :=
  {f | ∀ v x, frame a v = some x → f v = x}

@[simp] theorem mem_frameConstraint {frame : A → V → Option W} {a : A}
    {f : V → W} :
    f ∈ frameConstraint frame a ↔ ∀ v x, frame a v = some x → f v = x :=
  Iff.rfl

/-- **Pairwise compatibility on a variable.** Authors `a` and `b` are
compatible on `v` unless both fix `v`, to different values. Written as a
disjunction so the kernel can decide it. -/
def compatibleOn (frame : A → V → Option W) (v : V) (a b : A) : Prop :=
  frame a v = none ∨ frame b v = none ∨ frame a v = frame b v

instance instDecidableCompatibleOn [DecidableEq W] (frame : A → V → Option W)
    (v : V) (a b : A) : Decidable (compatibleOn frame v a b) := by
  unfold compatibleOn; infer_instance

/-- **Consistency of a frame corpus**: no two authors clash on any
variable. This is the decidable surrogate for feasibility. -/
def Consistent (frame : A → V → Option W) : Prop :=
  ∀ v a b, compatibleOn frame v a b

instance instDecidableConsistent [Fintype V] [Fintype A] [DecidableEq W]
    (frame : A → V → Option W) : Decidable (Consistent frame) := by
  unfold Consistent; infer_instance

/-- Compatibility forces agreement wherever both authors speak. -/
theorem eq_of_compatibleOn {frame : A → V → Option W} {v : V} {a b : A}
    (h : compatibleOn frame v a b) {x y : W}
    (ha : frame a v = some x) (hb : frame b v = some y) : x = y := by
  rcases h with h | h | h
  · exact absurd (ha ▸ h) (Option.some_ne_none x)
  · exact absurd (hb ▸ h) (Option.some_ne_none y)
  · rw [ha, hb] at h; exact Option.some.inj h

/-- Any assignment in both authors' property sets witnesses their
compatibility: satisfiability implies pairwise compatibility. -/
theorem compatibleOn_of_mem {frame : A → V → Option W} {v : V} {a b : A}
    {f : V → W} (ha : f ∈ frameConstraint frame a)
    (hb : f ∈ frameConstraint frame b) : compatibleOn frame v a b := by
  rcases hfa : frame a v with _ | x
  · exact Or.inl hfa
  · rcases hfb : frame b v with _ | y
    · exact Or.inr (Or.inl hfb)
    · have hx := (mem_frameConstraint.mp ha) v x hfa
      have hy := (mem_frameConstraint.mp hb) v y hfb
      exact Or.inr (Or.inr (by rw [hfa, hfb, ← hx, ← hy]))

/-- **Soundness of the surrogate**: if the feasibility set is nonempty,
the corpus is consistent. -/
theorem consistent_of_nonempty {frame : A → V → Option W}
    (h : (feasibilitySet (frameConstraint frame)).Nonempty) :
    Consistent frame := by
  obtain ⟨f, hf⟩ := h
  intro v a b
  exact compatibleOn_of_mem (mem_feasibilitySet.mp hf a) (mem_feasibilitySet.mp hf b)

/-- **The canonical reading built from a consistent corpus.** For each
variable take some author's asserted value (any will do, by consistency);
fall back to `default` where every author is silent. Noncomputable (it
chooses a witness), used only to prove the converse. -/
open Classical in
noncomputable def frameWitness [Inhabited W] (frame : A → V → Option W) :
    V → W :=
  fun v => if h : ∃ p : A × W, frame p.1 v = some p.2 then h.choose.2 else default

/-- The canonical reading satisfies every author's property set, provided
the corpus is consistent. -/
theorem frameWitness_mem [Inhabited W] {frame : A → V → Option W}
    (hcon : Consistent frame) (a : A) :
    frameWitness frame ∈ frameConstraint frame a := by
  refine mem_frameConstraint.mpr ?_
  intro v x hax
  have hex : ∃ p : A × W, frame p.1 v = some p.2 := ⟨(a, x), hax⟩
  have hval : frameWitness frame v = hex.choose.2 := by
    simp only [frameWitness, dif_pos hex]
  rw [hval]
  exact (eq_of_compatibleOn (hcon v a hex.choose.1) hax hex.choose_spec).symm

/-- **Completeness of the surrogate**: a consistent corpus has a nonempty
feasibility set (witnessed by `frameWitness`). -/
theorem nonempty_of_consistent [Inhabited W] {frame : A → V → Option W}
    (hcon : Consistent frame) :
    (feasibilitySet (frameConstraint frame)).Nonempty :=
  ⟨frameWitness frame, mem_feasibilitySet.mpr (fun a => frameWitness_mem hcon a)⟩

/-- **The exact bridge**: `Set`-level feasibility (nonempty) is equivalent
to the decidable, pairwise `Consistent`. -/
theorem nonempty_iff_consistent [Inhabited W] {frame : A → V → Option W} :
    (feasibilitySet (frameConstraint frame)).Nonempty ↔ Consistent frame :=
  ⟨consistent_of_nonempty, nonempty_of_consistent⟩

/-- **The computable feasibility verdict.** The verified `Set`-based
feasibility set of the corpus is empty iff the corpus is inconsistent --
and the right-hand side is decided by the kernel. -/
theorem feasibilitySet_eq_empty_iff [Inhabited W] {frame : A → V → Option W} :
    feasibilitySet (frameConstraint frame) = ∅ ↔ ¬ Consistent frame := by
  rw [← Set.not_nonempty_iff_eq_empty, nonempty_iff_consistent]

/-! ### The quantitative invariant: disagreement degree -/

/-- The set of distinct values a variable `v` actually receives across all
authors (silence contributes nothing). -/
def assertedValues [Fintype A] [DecidableEq W] (frame : A → V → Option W)
    (v : V) : Finset W :=
  (Finset.univ.image (fun a => frame a v)).eraseNone

@[simp] theorem mem_assertedValues [Fintype A] [DecidableEq W]
    {frame : A → V → Option W} {v : V} {x : W} :
    x ∈ assertedValues frame v ↔ ∃ a, frame a v = some x := by
  simp only [assertedValues, Finset.mem_eraseNone, Finset.mem_image,
    Finset.mem_univ, true_and]

/-- **Disagreement degree** of a variable: how many distinct values it is
assigned across the corpus. Degree `0` = nobody speaks, `1` = unanimous
where spoken, `≥ 2` = a genuine conflict site. -/
def disagreementDegree [Fintype A] [DecidableEq W] (frame : A → V → Option W)
    (v : V) : ℕ :=
  (assertedValues frame v).card

/-- **The per-variable agreement characterization**: a variable's spoken
values are unanimous iff its disagreement degree is at most one. This is
the decidable, quantitative refinement of pairwise compatibility. -/
theorem agree_iff_degree_le_one [Fintype A] [DecidableEq W]
    {frame : A → V → Option W} {v : V} :
    disagreementDegree frame v ≤ 1 ↔
      ∀ a b x y, frame a v = some x → frame b v = some y → x = y := by
  rw [disagreementDegree, Finset.card_le_one]
  constructor
  · intro h a b x y hax hby
    exact h x (mem_assertedValues.mpr ⟨a, hax⟩) y (mem_assertedValues.mpr ⟨b, hby⟩)
  · intro h x hx y hy
    obtain ⟨a, ha⟩ := mem_assertedValues.mp hx
    obtain ⟨b, hb⟩ := mem_assertedValues.mp hy
    exact h a b x y ha hb

end STE
