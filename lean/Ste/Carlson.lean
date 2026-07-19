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
-/
import Ste.Carlson.Cipher
import Ste.Carlson.Counting
import Ste.Carlson.Reduction
