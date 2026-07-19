# 2026-07-19 — Hypotheses: the STE core

Each hypothesis below is a proposition we conjectured from the seed papers
and then tried to discharge in Lean. Status is **PROVEN** only when the
statement compiles in the CI-checked `Ste` library; otherwise **OPEN**.

## H1 — Feasibility refines every constraint
*Claim:* $S=\bigcap_i S_i \subseteq S_j$ for every $j$; and $a\in S$ iff
$a$ satisfies every piece of information.
*Status:* **PROVEN** — `feasibilitySet_subset`, `mem_feasibilitySet`
(`Ste.Basic`). Direct from `Set.iInter_subset` / `Set.mem_iInter`.

## H2 — Information monotonicity
*Claim:* enforcing more constraints can only shrink the feasibility set:
$J\subseteq K \Rightarrow \bigcap_{i\in K}S_i \subseteq \bigcap_{i\in J}S_i$.
*Status:* **PROVEN** — `partialFeasibilitySet_antitone`. This is the
formal content of "more information never hurts feasibility" (Combettes)
and "more intercepted traffic only narrows the key search" (Carlson,
recovered as `feasibleKeys_antitone`).

## H3 — Fair information is consistent
*Claim:* if the truth $h$ satisfies every constraint ($h\in S_i$ for all
$i$), the problem is consistent ($S\ne\emptyset$).
*Status:* **PROVEN** — `feasibilitySet_nonempty_of_fair` via
`fair_iff_mem_feasibilitySet`.

## H4 — Inconsistency detects invalid information
*Claim:* $S=\emptyset$ implies that for every candidate truth $h$ some
property set excludes it (some piece of information is in error).
*Status:* **PROVEN** — `exists_unfair_of_feasibilitySet_eq_empty`.
Contrapositive of H3; this is the STE self-diagnostic (Combettes,
Fig.~1(a)).

## H5 — Ideal information identifies the estimand
*Claim:* if $S=\{h\}$ then every set theoretic estimate equals $h$;
and idealness $\iff$ (fair $\wedge$ feasibility is a subsingleton).
*Status:* **PROVEN** — `Ideal.eq_of_mem`,
`ideal_iff_fair_and_subsingleton`.

## H6 — Closedness / existence on topological spaces (Carlson's setting)
*Claim:* if every $S_i$ is closed then $S$ is closed; and on a
**compact** solution space, finite consistency (finite intersection
property) implies full consistency.
*Status:* **PROVEN** — `isClosed_feasibilitySet`,
`feasibilitySet_nonempty_of_compact` (`Ste.Topology`). The compactness
argument is the abstract reason STE is well posed on Carlson's finite
(discrete, hence compact) key spaces and on Combettes' bounded closed
convex constraints. Corollaries: `isClosed_feasibilitySet_of_discrete`,
`Ideal.isClosed_feasibilitySet` (T1).

## H7 — Convex feasibility (Combettes §III setting)
*Claim:* the intersection of convex property sets is convex.
*Status:* **PROVEN** — `convex_feasibilitySet`,
`convex_partialFeasibilitySet` (`Ste.Convex`). Prerequisite for a future
POCS convergence proof.

## H8 — STE decryption skeleton (Carlson)
*Claim:* genuine ciphertext traffic under a true key $k_0$ makes the
feasible key set nonempty (fair), and observation monotonicity holds;
"unicity" $=$ ideal information.
*Status:* **PROVEN** — `CipherSystem.fair_of_genuine`,
`feasibleKeys_nonempty_of_genuine`, `Unicity.eq_of_feasible`,
`feasibleKeys_antitone` (`Ste.Cipher`).

## OPEN targets (next sessions)
- **H9** Carlson Lemma 4.1 / Theorem 4.1: exact key counts
  $(|A|-|T|)!$ and $\binom{|S_t|}{C}(|B|-|S_t|)!$ — finite combinatorics,
  most tractable next target; needs a Lean model of substitution/
  permutation ciphers over `Fin`.
- **H10** Carlson Theorem 5.2 / Corollary 5.3: cipher reduction and
  "every block cipher is a block substitution cipher."
- **H11** POCS convergence for closed convex $S_i$ in a Hilbert space
  (Youla–Webb; Bauschke–Borwein), atop `Ste.Convex`.
- **H12** Carlson Theorem 2.3: property sets as AEP typical sets — the
  deepest result, ties information theory under STE; needs a probability
  model.
