# Proof 614: antiresonant geometric boundary resolvent

## Result

Proof 614 identifies Proof 613's geometric series as a genuine compressed
Euler renewal, rather than leaving it as an independently named sum.

For

```text
q = q_p,
E = radialSupportProjection,
V = E U_(log p) E,
C = (I - E) U_(log p) E,
G = sum_(n >= 0) q^(n+1) C V^n,
```

Lean proves

```text
G = q C + q G V,
G (I - q V) = q C,
G = q C sum_(n >= 0) (q V)^n.
```

The strict estimate `||q V|| < 1` makes the right denominator invertible.

## Genuine inverse-adjoint owner

Let

```text
N = normalizedPrimeEulerInverse(p),
R = E N^dagger E.
```

The negative-translation renewal `N` preserves the upper radial support.
Taking adjoints gives the precise no-reentry statement

```text
E N^dagger = E N^dagger E.
```

It does not say that `N^dagger` preserves the upper radial support. Using the
actual Euler inverse equation, Lean proves

```text
R (I - q V) = (1 - q) E,
R = (1 - q) E sum_(n >= 0) (q V)^n.
```

Therefore

```text
G = q / (1 - q) * C R
  = q / (1 - q) * C E N^dagger E.
```

Combining this with Proof 613 yields the direct actual-frame readback

```text
geometricReadout * ambientLoss^dagger * newFrame_S
  = q / (1 - q) * C E N^dagger E * newFrame_S,

||geometricReadout|| <= 32.
```

## Why this matters

```text
Proof 612              Proof 613                 Proof 614
block recurrence  -->  bounded geometric sum --> actual renewal owner
    C V^n                 ||readout|| <= 32        E N^dagger E
```

This removes an owner mismatch from the boundary lane. The controlled object
is now a real part of the source Euler coframe.

## Boundary of the result

The full raw numerator also contains the metric-coframe nonlinear Gram
correction and the coupled forward channel. Proof 614 does not identify those
terms with the geometric boundary and does not authorize estimating the two
leakages separately. Bone 1, Gate 3U, the finite-S sign, Burnol's identity,
and RH remain open.

## Verification

```text
focused source build: 3378 jobs, PASS
import-facing audit:  PASS
audited declarations: 15
axioms: [propext, Classical.choice, Quot.sound]

CCM25Concrete aggregate: 3882 jobs, PASS
full repository build:  3963 jobs, PASS
```
