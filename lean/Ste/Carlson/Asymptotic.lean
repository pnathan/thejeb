/-
Carlson's asymptotic decryption / unicity, mechanized in the crisp
(deterministic) setting.

Reference:
  A. H. Carlson, "Set Theoretic Estimation Applied to the Information
  Content of Ciphers and Decryption," Ph.D. dissertation, University of
  Idaho, May 2012.

Carlson's asymptotic unicity statement says that as intercepted
ciphertexts accumulate the STE feasibility set of consistent keys
collapses onto the true key.  This file mechanizes the deterministic
core of that claim:

  * `partialKeys` — the feasible key set after the first `n`
    observations of a ciphertext stream;
  * `AsymptoticUnicity` — that sequence is *eventually* the singleton
    `{k₀}`, equivalently (discrete topology) it converges to `{k₀}`;
  * over a finite key space the sequence stabilizes, so asymptotic
    unicity is equivalent to the total intersection being `{k₀}`,
    i.e. to unicity for the whole stream.

Honest scope note: Carlson's dissertation states the result almost
surely with respect to a source distribution on plaintexts.  The
measure-theoretic (a.s.) version is *not* attempted here; it is future
work and would require a probability space on message streams from
`Mathlib.MeasureTheory`.  Everything below is deterministic.
-/
import Ste.Basic
import Ste.Carlson.Cipher
import Mathlib.Topology.Instances.Discrete

namespace STE.Carlson

namespace CipherSystem

variable {K M C : Type*} (cs : CipherSystem K M C)

/-- The feasible key set after observing the first `n` ciphertexts of the
stream `obs`. -/
def partialKeys (Meaning : Set M) (obs : ℕ → C) (n : ℕ) : Set K :=
  STE.partialFeasibilitySet (fun i => cs.keyPropertySet Meaning (obs i)) {i | i < n}

/-- **Asymptotic unicity** (deterministic form): from some point on, the
feasible key set after `n` observations is exactly the true key. -/
def AsymptoticUnicity (Meaning : Set M) (obs : ℕ → C) (k₀ : K) : Prop :=
  ∀ᶠ n in Filter.atTop, cs.partialKeys Meaning obs n = {k₀}

/-- More traffic can only narrow the key search. -/
theorem partialKeys_antitone (Meaning : Set M) (obs : ℕ → C) :
    Antitone (cs.partialKeys Meaning obs) :=
  fun _ _ h => STE.partialFeasibilitySet_antitone _ (fun _ hi => lt_of_lt_of_le hi h)

/-- Asymptotic unicity is genuine convergence of the partial feasibility
sets to `{k₀}` in the discrete topology on `Set K`. -/
theorem asymptoticUnicity_iff_tendsto (Meaning : Set M) (obs : ℕ → C) (k₀ : K) :
    cs.AsymptoticUnicity Meaning obs k₀ ↔
      letI : TopologicalSpace (Set K) := ⊥
      Filter.Tendsto (cs.partialKeys Meaning obs) Filter.atTop (nhds {k₀}) := by
  letI : TopologicalSpace (Set K) := ⊥
  haveI : DiscreteTopology (Set K) := ⟨rfl⟩
  rw [nhds_discrete, Filter.tendsto_pure]; rfl

/-- The intersection over all prefixes is the feasible key set for the
whole stream. -/
theorem iInter_partialKeys (Meaning : Set M) (obs : ℕ → C) :
    ⋂ n, cs.partialKeys Meaning obs n = cs.feasibleKeys Meaning obs := by
  ext k
  simp only [partialKeys, feasibleKeys, STE.partialFeasibilitySet, STE.feasibilitySet,
    Set.mem_iInter, Set.mem_setOf_eq]
  exact ⟨fun h i => h (i + 1) i (Nat.lt_succ_self i), fun h _ i _ => h i⟩

/-- Over a finite key space, asymptotic unicity is equivalent to unicity
for the entire observation stream: the shrinking sequence of partial
feasibility sets stabilizes, so "eventually `{k₀}`" and "the limit set is
`{k₀}`" coincide. -/
theorem asymptoticUnicity_iff [Finite K] (Meaning : Set M) (obs : ℕ → C) (k₀ : K) :
    cs.AsymptoticUnicity Meaning obs k₀ ↔
      (⋂ n, cs.partialKeys Meaning obs n) = {k₀} := by
  have hstab := STE.antitone_eventually_eq_iInter (cs.partialKeys_antitone Meaning obs)
  constructor
  · intro h
    obtain ⟨n, hn1, hn2⟩ := (h.and hstab).exists
    rw [← hn2, hn1]
  · intro h
    filter_upwards [hstab] with n hn
    rw [hn, h]

/-- Finite-key restatement against the stream feasible key set. -/
theorem asymptoticUnicity_iff_unicity [Finite K] (Meaning : Set M) (obs : ℕ → C)
    (k₀ : K) :
    cs.AsymptoticUnicity Meaning obs k₀ ↔ cs.Unicity Meaning obs k₀ := by
  rw [cs.asymptoticUnicity_iff Meaning obs k₀, cs.iInter_partialKeys Meaning obs]
  rfl

end CipherSystem

end STE.Carlson
