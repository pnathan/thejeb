# Insertion-induced frame splitting

## Research prompt

Can new frame information split an existing normalized frame? The motivating
case begins with two compatible descriptions, “the red car” and “the burgundy
car,” and later identifies them as a Toyota and a BMW.

## Correction to the working vocabulary

There are two different objects that had both been called a frame:

1. A **must-coreference class** is an equivalence class under identity in every
   feasible exact normalization. Under hard evidence addition, this quotient
   can be preserved or merged but cannot split, because the feasible world set
   only shrinks.
2. A **possible-coreference ambiguity envelope** contains claims that can share
   a frame in at least one feasible normalization. Its `MaySame` edges can be
   removed by evidence, so the envelope can shrink and its presentation
   components can split.

The second object is what the database user experiences as an unresolved
frame. The authoritative semantics cannot therefore be one partition decorated
only with uncertain pair markers. It is the feasible family of exact
partitions; `MustSame`, `MaySame`, `CannotSame`, and `Uncertain` are queries over
that family.

## STE statement

Let `Π_D` be the feasible family at corpus `D`. Insertion applies a property
set `S_e`:

```text
Π_(D+e) = Π_D ∩ S_e.
```

For the envelope `A_D(c) = {d | MaySame_D(c,d)}`, document inclusion `D ⊆ E`
implies `A_E(c) ⊆ A_D(c)`. If `c,d` were uncertain at `D` and cannot-corefer
at `E`, then `d ∈ A_D(c)` and `d ∉ A_E(c)`. In a finite claim universe this
makes the envelope cardinality decrease strictly.

## Two-claim witness

Initially the feasible partitions are:

```text
{{red, burgundy}}, {{red}, {burgundy}}.
```

The Toyota/BMW evidence activates the property that rejects the merged world,
leaving:

```text
{{red}, {burgundy}}.
```

The red-car envelope changes from `{red, burgundy}` to `{red}`. Its exact
reduction is one. This is a real split of an ambiguity-bearing presentation,
not a split of a previously forced semantic identity.

## Mechanization consequences

- Add `mayEnvelope`, `ResolvesApart`, the subset/split theorem, and finite
  cardinal bounds.
- Add a constructive Toyota/BMW model with two claims, two worlds, one newly
  active constraint, and an exact reduction theorem.
- Keep `CanonicalFrame` as the safe must-quotient.
- Treat connected components of `MaySame` only as presentation envelopes;
  `MaySame` is not transitive, so components are not the authoritative state.
- Future solver work should represent correlations among candidate partitions,
  not merely independent pair statuses.
