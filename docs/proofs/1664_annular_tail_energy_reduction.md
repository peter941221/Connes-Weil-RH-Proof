# 1664 - Annular tail energy reduction

Date: 2026-09-19.

Status: formal conditional reduction. RH is not claimed.

## Result

The source-compressed root producer is reduced one step further.  Choose a
natural `N` beyond the selected root support radius and write the windowed
operator as

```text
A_n = A_N + (A_n - A_N),
      A_n = J† P_n C J.
```

The fixed term `A_N` has square-summable source columns by the compact-kernel
finite-window theorem.  A two-term norm estimate then shows that a uniform
finite-set energy bound for the annular difference `A_n - A_N`, for all
`n >= N`, implies a uniform finite-window bound for `A_n`.  The reverse-limit
criterion consequently gives square-summability of the uncut
source-compressed root.

## Lean declarations

```text
eventual_uniform_finite_window_energy_of_fixed_plus_tail
sourceCompressedRoot_squareSum_of_eventual_annular_energy
```

The second declaration consumes the concrete annular estimate

```text
Σ i in s, ||(J† P_n C J - J† P_N C J)e_i||² <= B
```

for every finite source-basis set `s` and every `n >= N`.

## Evidence

Build log: `1664_annular_consumer_green`.

The owning module and audit completed successfully (3962 jobs), with no
`error:`, no `sorryAx`, and only `[propext, Classical.choice, Quot.sound]`.

## Boundary

The annular estimate itself remains open.  This record does not introduce a
universal B1 argument, a ROOT density lift, a numerical premise, or an RH
conclusion.  It serves the healthy-`CompactLog` B5 source-compressed survivor
energy consumer.
