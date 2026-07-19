# thejeb

Machine-checked mechanization of **set theoretic estimation** (STE), seeded by:

- P. L. Combettes, *The Foundations of Set Theoretic Estimation*,
  Proceedings of the IEEE 81(2):182–208, 1993. doi:10.1109/5.214546
- A. H. Carlson, *Set Theoretic Estimation Applied to the Information Content
  of Ciphers and Decryption*, Ph.D. dissertation, University of Idaho, May 2012.

Operating rules for this project: work is committed to `main`; every claim is
cited; results are distrusted until machine-proven (Lean 4 + Mathlib, checked
in CI on every push to `main`); papers are written in LaTeX and built.

## Layout

- `sources/` — copies of the source PDFs
- `annotated-bibliography.tex` — annotated bibliography
- `lean/` — the Lean 4 mechanization (library `Ste`, Mathlib pinned)
- `log/` — dated work logs, one file per hypothesis/session
- `papers/notes/` — working notes, including the literature review
- `papers/papers/` — summary papers

## Lean

```
cd lean && lake exe cache get && lake build
```

CI: `.github/workflows/lean.yml` builds the `Ste` library with
[lean-action](https://github.com/leanprover/lean-action) on every push to `main`.
