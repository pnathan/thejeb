/-
Carlson's set-theoretic-estimation cryptanalysis, mechanized.

Reference:
  A. H. Carlson, "Set Theoretic Estimation Applied to the Information
  Content of Ciphers and Decryption," Ph.D. dissertation, University of
  Idaho, May 2012.

This module gathers:
  * `Ste.Carlson.Cipher`    — the STE-as-decryption skeleton (property
                              sets of keys, feasible keys, unicity).
  * `Ste.Carlson.Counting`  — Lemma 4.1, the residual key count
                              `(|A| - |T|)!`.
  * `Ste.Carlson.Reduction` — Theorem 5.2 / Lemma 5.1 / Corollary 5.3,
                              the reduction of ciphers to substitution
                              ciphers.
  * `Ste.Carlson.Asymptotic` — asymptotic unicity for a ciphertext
                              stream (deterministic form).
  * `Ste.Carlson.SheafBridge` — the bridge from the cipher STE picture to
                              the project's support / variable-presheaf
                              layer (scoped decryption constraints,
                              `keyPropertySet` as a decryption
                              constraint, non-rectangularity of the key
                              coupling, residual keys as a restriction
                              fiber).
  * `Ste.Carlson.SetOfSets`  — the second-order extension: sources that
                              contribute a set of candidate possibility
                              sets rather than a single one.
-/
import Ste.Carlson.Cipher
import Ste.Carlson.Counting
import Ste.Carlson.Reduction
import Ste.Carlson.Asymptotic
import Ste.Carlson.SheafBridge
import Ste.Carlson.SetOfSets
