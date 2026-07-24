/-
An empirical instance of set-theoretic estimation: the multi-voice
"cause of the tides" corpus, mechanized.

The seven authors of `sources/tides/` (Pliny, Bede, Kepler, Galileo,
Descartes, Newton, Laplace) were extracted into a canonical 7-variable
schema by a three-pass pipeline (Haiku open extraction -> Sonnet schema
unification -> Haiku schema-constrained re-extraction;
`sources/tides/extraction/frames.json`, `scripts/tides/`). This module
encodes those frames verbatim as STE property sets and machine-checks
the invariants of the disagreement, tying them to `Ste.Basic`
(`feasibilitySet`, Combettes 1993).

Each author `a` asserts a partial assignment `frame a : Var -> Option Val`
(silence = `none`); the property set `constraint a` is the set of total
assignments agreeing with `a` wherever `a` speaks. The STE feasibility
set is `feasibilitySet constraint = ⋂ a, constraint a`.

**What the corpus turns out to be** (all proved below):

* `feasible_eq_empty` -- the corpus is globally *inconsistent*: no single
  reading satisfies all seven voices.
* The obstruction is carried by `moonRole`, which splits three ways:
  attraction / pressure / rejected. Any two authors in different camps
  are already a minimal conflicting core (`kepler_galileo_core`,
  `kepler_descartes_core`, `galileo_descartes_core`).
* The disagreement is *pervasive*, not a single outlier: even the
  five-author attraction camp is internally inconsistent on `mechanism`
  (`pliny_kepler_mechanism_core`).
* Positive structure: on the single most-contested variable `moonRole`,
  the attraction camp has a common reading
  (`attraction_camp_moon_consistent`) and exactly two voices dissent --
  Descartes (pressure) and Galileo (rejected)
  (`descartes_dissents`, `galileo_dissents`).
* `no_fair_reading` -- the Combettes corollary: an inconsistent
  formulation proves every candidate estimand is unfair to some voice.

Reference: P. L. Combettes, "The Foundations of Set Theoretic
Estimation," Proc. IEEE 81(2), 1993. Corpus provenance: `refs.bib`
(pliny77naturalis, bede725temporum, kepler1609astronomia,
galileo1632dialogue, descartes1644principia, newton1687principia,
laplace1799mecanique).
-/
import Ste.Basic

namespace STE.Tides

open STE

/-- The seven canonical variables (the topic's relations). -/
inductive Var
  | primaryCause | moonRole | mechanism | sunRole | springNeap
  | earthMotion | quantitative
  deriving DecidableEq

/-- The union of all domain values across the seven variables. -/
inductive Val
  | moon | sunAndMoon | earthMotionCause                    -- primary_cause
  | attraction | pressure | rejected                        -- moon_role
  | directCorrespondence | gravitationalAttraction          -- mechanism …
  | basinMotion | pressureOfVortex | dynamicalOscillation
  | reinforcesAtSyzygy | weakerThanMoon                     -- sun_role
  | springsAtSyzygy | neapsAtQuadrature                     -- spring_neap
  | required                                                -- earth_motion_required
  | mathematized                                            -- quantitative
  deriving DecidableEq

/-- The seven authors (the index set of pieces of information). -/
inductive Author
  | pliny | bede | kepler | galileo | descartes | newton | laplace
  deriving DecidableEq

/-- A total assignment of a value to every variable. -/
abbrev Assign := Var → Val

/-- **The extracted frames**, verbatim from
`sources/tides/extraction/frames.json`: each author's asserted value per
variable, `none` where the author is silent. -/
def frame : Author → Var → Option Val
  | .pliny, .primaryCause => some .sunAndMoon
  | .pliny, .moonRole => some .attraction
  | .pliny, .mechanism => some .directCorrespondence
  | .pliny, .sunRole => some .reinforcesAtSyzygy
  | .pliny, .springNeap => some .springsAtSyzygy
  | .bede, .primaryCause => some .moon
  | .bede, .moonRole => some .attraction
  | .bede, .mechanism => some .directCorrespondence
  | .bede, .springNeap => some .springsAtSyzygy
  | .kepler, .primaryCause => some .moon
  | .kepler, .moonRole => some .attraction
  | .kepler, .mechanism => some .gravitationalAttraction
  | .galileo, .primaryCause => some .earthMotionCause
  | .galileo, .moonRole => some .rejected
  | .galileo, .mechanism => some .basinMotion
  | .galileo, .earthMotion => some .required
  | .descartes, .primaryCause => some .sunAndMoon
  | .descartes, .moonRole => some .pressure
  | .descartes, .mechanism => some .pressureOfVortex
  | .descartes, .sunRole => some .reinforcesAtSyzygy
  | .descartes, .springNeap => some .springsAtSyzygy
  | .newton, .primaryCause => some .sunAndMoon
  | .newton, .moonRole => some .attraction
  | .newton, .mechanism => some .gravitationalAttraction
  | .newton, .sunRole => some .weakerThanMoon
  | .newton, .springNeap => some .springsAtSyzygy
  | .newton, .quantitative => some .mathematized
  | .laplace, .primaryCause => some .sunAndMoon
  | .laplace, .moonRole => some .attraction
  | .laplace, .mechanism => some .dynamicalOscillation
  | .laplace, .quantitative => some .mathematized
  | _, _ => none

/-- **The property set of author `a`** (Combettes' `Sᵢ`): the total
assignments agreeing with `a`'s frame wherever `a` speaks. -/
def constraint (a : Author) : Set Assign :=
  {f | ∀ v x, frame a v = some x → f v = x}

@[simp] theorem mem_constraint {a : Author} {f : Assign} :
    f ∈ constraint a ↔ ∀ v x, frame a v = some x → f v = x := Iff.rfl

/-! ### Global inconsistency and the minimal conflicting cores -/

/-- **A two-author minimal core.** Kepler (moon *attraction*) and Galileo
(moon-role *rejected*) already have disjoint property sets: no assignment
can make `moonRole` both `attraction` and `rejected`. -/
theorem kepler_galileo_core :
    constraint .kepler ∩ constraint .galileo = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  rintro f ⟨hk, hg⟩
  have h1 := (mem_constraint.mp hk) .moonRole .attraction rfl
  have h2 := (mem_constraint.mp hg) .moonRole .rejected rfl
  rw [h1] at h2
  exact absurd h2 (by decide)

/-- Kepler (attraction) vs Descartes (pressure): a second minimal core on
`moonRole`. -/
theorem kepler_descartes_core :
    constraint .kepler ∩ constraint .descartes = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  rintro f ⟨hk, hd⟩
  have h1 := (mem_constraint.mp hk) .moonRole .attraction rfl
  have h2 := (mem_constraint.mp hd) .moonRole .pressure rfl
  rw [h1] at h2
  exact absurd h2 (by decide)

/-- Galileo (rejected) vs Descartes (pressure): the third pair of the
three-way `moonRole` split is also a minimal core. -/
theorem galileo_descartes_core :
    constraint .galileo ∩ constraint .descartes = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  rintro f ⟨hg, hd⟩
  have h1 := (mem_constraint.mp hg) .moonRole .rejected rfl
  have h2 := (mem_constraint.mp hd) .moonRole .pressure rfl
  rw [h1] at h2
  exact absurd h2 (by decide)

/-- **Global inconsistency**: the STE feasibility set of the whole corpus
is empty -- no single reading of the tides satisfies all seven voices.
It follows from any one minimal core. -/
theorem feasible_eq_empty : feasibilitySet constraint = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  intro f hf
  have hk : f ∈ constraint .kepler := mem_feasibilitySet.mp hf .kepler
  have hg : f ∈ constraint .galileo := mem_feasibilitySet.mp hf .galileo
  have hfe : f ∈ constraint .kepler ∩ constraint .galileo := ⟨hk, hg⟩
  rw [kepler_galileo_core] at hfe
  exact hfe

/-- **The disagreement is pervasive, not a single outlier.** Even within
the five-author *attraction* camp, Pliny (mechanism *direct
correspondence*) and Kepler (mechanism *gravitational attraction*) are a
minimal conflicting core -- so removing Galileo and Descartes does not
restore consistency. -/
theorem pliny_kepler_mechanism_core :
    constraint .pliny ∩ constraint .kepler = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  rintro f ⟨hp, hk⟩
  have h1 := (mem_constraint.mp hp) .mechanism .directCorrespondence rfl
  have h2 := (mem_constraint.mp hk) .mechanism .gravitationalAttraction rfl
  rw [h1] at h2
  exact absurd h2 (by decide)

/-! ### Positive structure on the most-contested variable -/

/-- The `moonRole`-only property set of author `a`: what `a` demands of an
assignment's `moonRole` coordinate alone. -/
def moonConstraint (a : Author) : Set Assign :=
  {f | ∀ x, frame a .moonRole = some x → f .moonRole = x}

@[simp] theorem mem_moonConstraint {a : Author} {f : Assign} :
    f ∈ moonConstraint a ↔ ∀ x, frame a .moonRole = some x → f .moonRole = x :=
  Iff.rfl

/-- The "attraction reading": the assignment sending every variable to
`attraction` (only its `moonRole` coordinate matters here). -/
def attractionReading : Assign := fun _ => Val.attraction

/-- The attraction reading satisfies the `moonRole` demand of any author
whose frame fixes `moonRole` to `attraction`. -/
theorem attractionReading_mem {a : Author}
    (ha : frame a .moonRole = some .attraction) :
    attractionReading ∈ moonConstraint a := by
  refine mem_moonConstraint.mpr ?_
  intro x hx
  rw [ha] at hx
  injection hx with e
  exact e

/-- **The attraction camp shares a `moonRole` reading.** On the single
most-contested variable, the five attraction authors (Pliny, Bede,
Kepler, Newton, Laplace) are mutually consistent -- witnessed by the
attraction reading. -/
theorem attraction_camp_moon_consistent :
    attractionReading ∈ moonConstraint .pliny ∧
    attractionReading ∈ moonConstraint .bede ∧
    attractionReading ∈ moonConstraint .kepler ∧
    attractionReading ∈ moonConstraint .newton ∧
    attractionReading ∈ moonConstraint .laplace :=
  ⟨attractionReading_mem rfl, attractionReading_mem rfl,
   attractionReading_mem rfl, attractionReading_mem rfl,
   attractionReading_mem rfl⟩

/-- **Descartes dissents** from the attraction reading on `moonRole`
(he demands *pressure*). -/
theorem descartes_dissents : attractionReading ∉ moonConstraint .descartes := by
  intro h
  have := (mem_moonConstraint.mp h) .pressure rfl
  exact absurd this (by decide)

/-- **Galileo dissents** from the attraction reading on `moonRole`
(he *rejects* the moon's role). -/
theorem galileo_dissents : attractionReading ∉ moonConstraint .galileo := by
  intro h
  have := (mem_moonConstraint.mp h) .rejected rfl
  exact absurd this (by decide)

/-! ### The Combettes corollary -/

/-- **No fair reading exists.** Since the corpus is inconsistent, every
candidate estimand fails at least one voice -- the set-theoretic
detection-of-invalid-information principle (Combettes 1993, §II-C),
instantiated on the tides corpus. -/
theorem no_fair_reading (h : Assign) : ∃ a, h ∉ constraint a :=
  exists_unfair_of_feasibilitySet_eq_empty feasible_eq_empty h

end STE.Tides
