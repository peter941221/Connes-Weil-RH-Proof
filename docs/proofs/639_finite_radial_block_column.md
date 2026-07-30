# Proof 639: finite radial-block column

## Result

For every visible prime `p`, suffix `S`, and block count `N`, Proof 639 puts
the first `N` Euler-weighted radial boundary cells in one orthogonal
`PiLp 2` column.  Write

```text
q_p = ccm24PrimeEulerCoefficient(p) = p^(-1/2).
```

The exact factorization is

```text
finiteRadialReadoutColumn_(p,N)
    * (L_p^dagger * newFrame_(p,S))
  = finiteRadialBoundaryColumn_(p,S,N).
```

The readout is uniform in both parameters:

```text
||finiteRadialReadoutColumn_(p,N)|| <= 32.
```

Consequently, pointwise,

```text
||finiteRadialBoundaryColumn_(p,S,N) x||
  <= 32 ||L_p^dagger newFrame_(p,S) x||.
```

## Why the column matters

Proof 612 recovered one radial cell at a time.  An unweighted `n`th readout
has the raw cost

```text
||B_n|| <= ||lossScale_p^-1|| (n + 1),
```

whose `lossScale_p^-1` factor grows like `p^(1/4)`.  Proof 639 inserts the
actual Euler coefficient before measuring the column.  The `n`th coordinate
then has the family-independent majorant

```text
2 (n + 1) (3/4)^n.
```

These majorants have total sum `32`.  The `PiLp 2` norm retains the physical
cells as orthogonal coordinates, and the elementary inequality

```text
sum a_n^2 <= (sum a_n)^2
```

therefore gives the same bound `32` for every finite truncation.  There is no
factor depending on `N`.

```text
 raw right co-defect column
          |
          v
 +----------------------------------+
 | q B_0, q^2 B_1, ..., q^N B_(N-1)|  PiLp 2 readout
 +----------------------------------+
          |
          v
 +----------------------------------+
 | q C u, q^2 C V u, ..., q^N C V^(N-1)u |
 +----------------------------------+
```

## Boundary

This closes the finite radial-window denominator handoff.  It does not prove
that the complete local raw-defect pair lands in this radial block column.
In particular, the second-support and prolate terms remain coupled and must
not be estimated as separate Hilbert--Schmidt legs.  Bone 1, Gate 3U, the
finite-S sign, Burnol's identity, and RH remain open.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorFiniteRadialBlockColumn.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorFiniteRadialBlockColumnAudit.lean
```

## Verification

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| finite radial-block column source    |  3378 | PASS   |
| focused eight-declaration audit      |     - | PASS   |
+--------------------------------------+-------+--------+
```

All eight audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.
