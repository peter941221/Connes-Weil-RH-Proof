# 1665 - Annular operator energy interface

Date: 2026-09-19.

Status: formal conditional reduction. RH is not claimed.

## Result

The expanding-window difference is now an explicit operator:

```text
Annular(N,n) = J† (P_n - P_N) C J.
```

Lean proves the exact identity `A_n - A_N = Annular(N,n)`, where
`A_n = J† P_n C J`, and proves square-summability of every fixed annular
operator once both endpoint windows contain the selected root support.

The source-root producer now consumes the direct annular estimate: for some
support threshold `N` and constant `B`, every `n >= N` and every finite source
basis set must satisfy

```text
Σ i in s, ||Annular(N,n)e_i||² <= B.
```

This implies the full source-compressed root square-sum by the fixed-window
plus-tail estimate and the reverse-limit criterion.

## Lean evidence

Declarations:

```text
sourceCompressedRootAnnularWindow
sourceCompressedRootFiniteWindow_sub_eq_annularWindow
sourceCompressedRootAnnularWindow_sourceBasis_normSq_summable
sourceCompressedRoot_squareSum_of_eventual_annular_energy
```

Build log: `1665_annular_operator_final`.

The owning module and audit completed successfully (3962 jobs), with no
`error:`, no `sorryAx`, and only `[propext, Classical.choice, Quot.sound]`.

## Boundary

The uniform-in-radius annular estimate remains open. No numerical premise,
universal B1 lift, or RH conclusion is introduced.
