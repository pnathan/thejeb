/-
Set theoretic estimation applied to decryption.

Reference:
  A. H. Carlson, "Set Theoretic Estimation Applied to the Information
  Content of Ciphers and Decryption," Ph.D. dissertation, Computer
  Science, University of Idaho, May 2012 (advisors R. E. Hiromoto and
  R. B. Wells).  Carlson recasts Shannon-style decryption as an STE
  problem: the solution space is the (finite) key space, each observed
  ciphertext contributes the property set of keys under which it
  decrypts to a meaningful message, and decryption succeeds when the
  feasibility set collapses to the true key (Shannon's unicity).

This file mechanizes the skeleton of that reduction on top of
`Ste.Basic`.  Quantitative results (unicity distance, equivocation)
are future work; see papers/notes.
-/
import Mathlib.Data.Set.Lattice
import Ste.Basic

namespace STE

/-- A cipher system: a keyed family of injective encryption maps from
messages to ciphertexts.  Injectivity in the message argument is the
minimal requirement for well defined decryption. -/
structure CipherSystem (K M C : Type*) where
  /-- Encryption under a key. -/
  enc : K → M → C
  /-- Each key's encryption map is injective, so decryption under a
  known key is unambiguous. -/
  enc_injective : ∀ k, Function.Injective (enc k)

namespace CipherSystem

variable {K M C : Type*} (cs : CipherSystem K M C)

/-- Decryption under a key is unambiguous: a ciphertext has at most one
plaintext per key. -/
theorem decrypt_unique {k : K} {m m' : M} {c : C}
    (h : cs.enc k m = c) (h' : cs.enc k m' = c) : m = m' :=
  cs.enc_injective k (h.trans h'.symm)

/-- The property set on keys induced by observing the ciphertext `c`,
relative to a set `Meaning ⊆ M` of meaningful (recognizable) messages:
the keys under which `c` is the encryption of some meaningful message.
This is Carlson's STE property set, and Shannon's set of "residual
keys" after one observation. -/
def keyPropertySet (Meaning : Set M) (c : C) : Set K :=
  {k | ∃ m ∈ Meaning, cs.enc k m = c}

variable {ι : Type*}

/-- The feasible key set after a family of ciphertext observations
`obs : ι → C`: exactly the STE feasibility set of the induced property
sets. -/
def feasibleKeys (Meaning : Set M) (obs : ι → C) : Set K :=
  feasibilitySet fun i => cs.keyPropertySet Meaning (obs i)

/-- A key is feasible iff every observed ciphertext decrypts under it
to some meaningful message. -/
theorem mem_feasibleKeys {Meaning : Set M} {obs : ι → C} {k : K} :
    k ∈ cs.feasibleKeys Meaning obs ↔
      ∀ i, ∃ m ∈ Meaning, cs.enc k m = obs i :=
  mem_feasibilitySet

/-- **Fairness of genuine traffic**: if the observations really are
encryptions of meaningful messages under a true key `k₀`, then the
induced information is fair for `k₀`; in particular the feasible key
set is nonempty and STE decryption is consistent (Carlson 2012, the
validity of the STE recast; Combettes 1993 §II-C). -/
theorem fair_of_genuine {Meaning : Set M} {obs : ι → C} {k₀ : K}
    (msg : ι → M) (hmean : ∀ i, msg i ∈ Meaning)
    (hobs : ∀ i, cs.enc k₀ (msg i) = obs i) :
    Fair (fun i => cs.keyPropertySet Meaning (obs i)) k₀ :=
  fun i => ⟨msg i, hmean i, hobs i⟩

/-- Genuine traffic makes the feasible key set nonempty. -/
theorem feasibleKeys_nonempty_of_genuine {Meaning : Set M} {obs : ι → C}
    {k₀ : K} (msg : ι → M) (hmean : ∀ i, msg i ∈ Meaning)
    (hobs : ∀ i, cs.enc k₀ (msg i) = obs i) :
    (cs.feasibleKeys Meaning obs).Nonempty :=
  feasibilitySet_nonempty_of_fair (cs.fair_of_genuine msg hmean hobs)

/-- **Unicity**: the observations identify the key when the induced
information is ideal, i.e. the feasible key set is exactly `{k₀}`.
This is the set theoretic form of Shannon's unicity point (Carlson
2012). -/
def Unicity (Meaning : Set M) (obs : ι → C) (k₀ : K) : Prop :=
  Ideal (fun i => cs.keyPropertySet Meaning (obs i)) k₀

/-- At unicity, every feasible key is the true key: STE decryption
succeeds by feasibility alone. -/
theorem Unicity.eq_of_feasible {Meaning : Set M} {obs : ι → C} {k₀ k : K}
    (hu : cs.Unicity Meaning obs k₀)
    (hk : k ∈ cs.feasibleKeys Meaning obs) : k = k₀ :=
  Ideal.eq_of_mem hu hk

/-- **Observation monotonicity**: enlarging the set of enforced
observations never enlarges the feasible key set — the formal content
of "more intercepted traffic can only narrow the key search" (Shannon;
Carlson 2012, STE recast).  Special case of
`STE.partialFeasibilitySet_antitone`. -/
theorem feasibleKeys_antitone {Meaning : Set M} {obs : ι → C}
    {J J' : Set ι} (hJJ' : J ⊆ J') :
    partialFeasibilitySet (fun i => cs.keyPropertySet Meaning (obs i)) J' ⊆
      partialFeasibilitySet (fun i => cs.keyPropertySet Meaning (obs i)) J :=
  partialFeasibilitySet_antitone _ hJJ'

end CipherSystem

end STE
