# Proof 617: signed radial interior reduction

## Result

Proof 617 shows that the complete old-carrier signed row cannot see the
exterior adjoint renewal at all.

Let

```text
E = radialSupportProjection,
F = I - E,
N = normalizedPrimeEulerInverse(p),
X = F N^dagger E,
R = E N^dagger E.
```

The actual old suffix frame lies in the radial range. Therefore

```text
oldFrame^dagger F = 0.
```

Every term of the complete signed telescope ends in `oldFrame^dagger`, so
Lean proves

```text
signedRow * F = 0,
signedRow * E = signedRow,
signedRow * X = 0.
```

Combining the last identity with Proof 616 also gives

```text
signedRow * exteriorReadout * ambientLoss^dagger * E = 0.
```

The exterior channel is therefore exactly absent from the signed numerator;
it is not merely bounded by `32`.

## Interior survivor

For the genuine inverse-adjoint pullback, the signed row reduces exactly to
the compressed interior renewal:

```text
signedRow * N^dagger * E
  = signedRow * E N^dagger E
  = signedRow * R.
```

The same compression holds for the scalar-normalized right inverse used by
the active coframe normal form, both globally and after the actual new frame.

```text
signedRow * V_scalar^dagger
  = signedRow * E * V_scalar^dagger.
```

## Route consequence

```text
+---------------------------------------+-------------------------------+
| channel                               | status                        |
+---------------------------------------+-------------------------------+
| exterior renewal F N^dagger E         | exactly annihilated           |
| geometric boundary C E N^dagger E     | readable, but not invertible  |
| interior renewal E N^dagger E         | sole antiresonant survivor    |
| metric/forward interior cancellation  | open                          |
| Bone 1 uniform factor                 | open                          |
+---------------------------------------+-------------------------------+
```

Proof 614 reads the boundary crossing `C R`; it does not recover `R` itself.
No lower bound or inverse for `C` is available. The next theorem must expand
`signedRow * R` as one coupled metric/forward interior object and use the
actual Sonin/Fourier plus compact-detector geometry before taking norms.

## Verification

```text
focused source build: 3381 jobs, PASS
import-facing audit:  PASS
audited declarations: 9
axioms: [propext, Classical.choice, Quot.sound]

CCM25Concrete aggregate: 3885 jobs, PASS
full repository build:  3966 jobs, PASS
```

## Boundary

Proof 617 eliminates one channel; it does not control the surviving interior
renewal. Bone 1, Gate 3U, the finite-S sign, Burnol's identity, and RH remain
open.
