# Proof 615: antiresonant exterior adjoint renewal

## Result

Proof 615 upgrades the geometric first-exit boundary from Proofs 613--614 to
the complete radial-interior-to-exterior block of the genuine adjoint Euler
renewal.

Set

```text
q = q_p,
E = radialSupportProjection,
F = I - E,
N = normalizedPrimeEulerInverse(p),
V = E U_(log p) E,
C = F U_(log p) E,
G = sum_(n >= 0) q^(n+1) C V^n,
X = F N^dagger E,
Y = F N^dagger F.
```

The lower-left radial block of the genuine Euler equation gives

```text
X (I - q V) = q Y C.
```

Proof 614 gives the matching boundary equation

```text
G (I - q V) = q C.
```

Because `||q V|| < 1`, the common right denominator is invertible. Lean
therefore proves the exact first-exit factorization

```text
X = Y G.
```

This is an identity for the actual exterior adjoint block. It is not a
formally defined remainder or a comparison with a model operator.

## Uniform readout

Both radial complements are orthogonal-projection complements, and the
normalized Euler inverse is contractive. Hence

```text
||Y|| = ||F N^dagger F|| <= 1.
```

Postcomposing Proof 613's geometric readout by `Y` preserves its family-wide
constant:

```text
exteriorReadout = Y * geometricReadout,
||exteriorReadout|| <= 32.
```

On every actual suffix frame, Lean proves

```text
exteriorReadout * ambientLoss^dagger * newFrame_S
  = F N^dagger E * newFrame_S.
```

Thus the complete exterior adjoint-renewal leakage channel is read from the
actual antiresonant ambient-loss column with a bound independent of the
visible prime, suffix list, and Sonin scale.

## Divide-and-conquer state

```text
+--------------------------------------+------------------------------+
| channel                              | status                       |
+--------------------------------------+------------------------------+
| geometric first-exit boundary G      | controlled, bound 32         |
| full exterior block F N^dagger E     | controlled, bound 32         |
| metric-coframe Gram correction       | open                         |
| coupled forward/metric remainder     | must remain combined         |
| complete signed numerator / Bone 1   | open                         |
+--------------------------------------+------------------------------+
```

The next source theorem must rewrite the complete signed numerator as this
controlled exterior channel plus a genuine, independently meaningful
metric/forward remainder. Defining the remainder only as "total minus known"
would not add mathematical control.

## Boundary of the result

Proof 615 does not identify the full signed numerator with the exterior
renewal. It does not bound the metric-coframe Gram correction, and it does not
authorize separate absolute-value estimates of the metric and forward legs.
Bone 1, Gate 3U, the finite-S sign, Burnol's identity, and RH remain open.

## Verification

```text
focused source build: 3379 jobs, PASS
import-facing audit:  PASS
audited declarations: 8
axioms: [propext, Classical.choice, Quot.sound]

CCM25Concrete aggregate: 3883 jobs, PASS
full repository build:  3964 jobs, PASS
```
