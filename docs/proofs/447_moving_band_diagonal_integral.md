# Proof 447: Moving-band finite diagonal integral

Date: 2026-07-20

## Result

The actual infinite-dimensional endpoint identity now has a legal scalar
readback on every Hilbert-space vector and every finite Hilbert-basis diagonal
truncation.

For one vector `u`, Lean proves

```text
integral_0^1 <u, actualMovingSoninRootFlow(alpha) u> d alpha
  = -<u, rootSandwichedBandResponse u>.
```

For a Hilbert basis `basis` and a finite index set `J`, taking real parts and
commuting only the finite sum with the interval integral gives

```text
sum_(i in J) Re <basis_i, rootSandwichedBandResponse basis_i>
  = -integral_0^1
      sum_(i in J) Re <basis_i, actualMovingSoninRootFlow(alpha) basis_i>
    d alpha.
```

The source module is:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSMovingBandDiagonalIntegral.lean
```

## Complete-crossing readback

At each legal synchronized time `|alpha| <= 1`, the diagonal flow density is
identified pointwise with the complete five-branch crossing:

```text
Re <u, actualMovingSoninRootFlow(alpha) u>
  = -2 Re <u, actualCompletedRootCrossing(alpha) u>.
```

Thus the scalar reduction preserves the radial deletion and the recombined
outer, Sonin, prolate, numerator, and inverse-Gram structure from Proof 445.
It does not replace that structure by a branchwise norm estimate.

## Why the truncation is legal

The single coefficient is obtained by applying a continuous linear functional
on the operator Banach space to Proof 446's Bochner integral.  The finite
diagonal theorem then uses only `intervalIntegral.integral_finsetSum`.

No infinite sum is exchanged with the integral.  In particular, this is not
a finite-matrix model and does not claim that finite sections prove the
continuous Gate 3U estimate.

## Remaining boundary

The next analytic producer must uniformly control these finite diagonal
signed integrals and justify passage to the full ordinary trace.  Diagonal
Euler energy alone remains insufficient because coherent synthesis can grow
quadratically.

Gate 3U, the finite-S sign, negative-owner integration, Burnol's identity,
and `_root_.RiemannHypothesis` remain open.

The focused audit is:

```text
ConnesWeilRH/Dev/
  CCM24FiniteSMovingBandDiagonalIntegralAudit.lean
```

## Verification

The Windows sources were copied one way into the cache-bearing Ubuntu 24.04
ext4 verification mirror.  The acceptance batch passed:

```text
+------------------------------------------------------+-------+--------+
| target                                               | jobs  | result |
+------------------------------------------------------+-------+--------+
| moving-band diagonal source build                    |  3211 | PASS   |
| CCM25Concrete aggregate                              |  3722 | PASS   |
| full repository / default lake build                 |  3803 | PASS   |
+------------------------------------------------------+-------+--------+
```

The focused audit prints exactly

```text
[propext, Classical.choice, Quot.sound]
```

for the one-vector, pointwise complete-crossing, and finite-diagonal
theorems.
