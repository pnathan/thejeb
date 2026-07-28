# Delsol, Rioul, Béguinot, Rabiet, Souloumiac (2024)

**An Information Theoretic Condition for Perfect Reconstruction.**
*Entropy* 26(1), 86. PMC10814784.

Full-text copy stored for the `thejeb` project:

- `PMC10814784.html` — verbatim PMC article page (downloaded 2026-07-28).
- `PMC10814784.txt`  — tag-stripped plain-text rendering of the same, for grep/reading.

## Why it is here

The paper develops **Shannon's 1953 lattice theory of information**: discrete
random variables up to equivalence, ordered by "is a deterministic function
of", forming a lattice (`∧` = common information, `∨` = joint information),
made **metric** by two entropic distances (Shannon's `D(X,Y)=H(X|Y)+H(Y|X)`
and Rajski's normalized `d`). Submodularity of entropy is shown compatible
with the lattice, and a geometric (metric) necessary/sufficient condition for
perfect reconstruction of `X` from functions `Xᵢ=fᵢ(X)` is derived.

This is the **same object** as the project's mechanized partition lattice
(`Ste.PartitionRank`): equivalence classes of a random variable ≅ partitions
of its sample space, "is a function of" ≅ refinement, `∨/∧` ≅ lattice
join/meet. The paper's submodularity-of-entropy is the measure-theoretic
parent of our combinatorial `rank_submodular`, and its entropic *metric* is
the parent of the combinatorial Shannon distance mechanized in
`Ste.InfoDistance`.

## Mechanization boundary (honest)

Mathlib has **no** general discrete Shannon entropy `H(X)`, conditional
entropy, or mutual information (only binary entropy, topological entropy, and
Kullback–Leibler). A faithful mechanization of the paper's *measure-theoretic*
proofs would require building that entire edifice first (PFR-scale). What is
faithfully mechanized here is the paper's **lattice / metric skeleton** in its
combinatorial (rank) shadow, which needs no entropy foundation: the partition
lattice is a metric space under the counting Shannon distance, with the four
metric axioms following from the already-proven rank submodularity and
monotonicity. The genuine entropy-valued distances and the reconstruction
theorems (Thm 1–4) are recorded as cited results, not reproved.
