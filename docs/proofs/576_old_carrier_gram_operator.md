# Proof 576: old-carrier Gram operator

## Result

Proof 575 identified the remaining target as a uniform Douglas estimate on
the old finite-S carrier.  Proof 576 computes the exact Gram operator of the
packed analysis map

```text
W = suffixEulerFrameAmbientBoundaryOldCarrierAnalysis
```

Write

```text
A = primeEulerAmbientLossFactor(p)
T = normalizedPrimeEulerFrameTransport(p)
N = (suffixEulerFrameSchurStep lambda p S).newFrame
P = N N†
```

Then the two channels give

```text
W† W = A A† + T (I-P) T†.
```

The existing ambient co-defect identity is

```text
A A† = I - T T†.
```

The new-frame isometry makes `P` an orthogonal projection, so

```text
W† W = I - T P T†.
```

This is an exact operator identity on the genuine global-log `L2` carrier.
It is not an estimate and does not identify the new-frame range with the
whole carrier.

## Diagram

```text
                         old-carrier Gram operator
                                  W† W
                                    |
              +---------------------+---------------------+
              |                                           |
       ambient loss channel                         boundary channel
              |                                           |
          A A† = I - T T†                         T (I-P) T†
              |                                           |
              +---------------------+---------------------+
                                    |
                            I - T P T†
                                    |
                                    v
                     exact positive operator (Gram)
```

The corresponding pointwise readback is

```text
||W y||^2 = Re <(I - T P T†) y, y>.
```

## Lean owner

`CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction.lean` proves:

```text
suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_adjoint_comp_self_eq_id_sub_transport_newProjection
suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_id_sub_transport_newProjection_nonneg
suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_normSq_eq_id_sub_transport_newProjection
```

The focused audit checks all three declarations.  Their only reported axioms
are `[propext, Classical.choice, Quot.sound]`.

## What this closes

The old-carrier target is now a single positive-operator comparison:

```text
||R0 y||^2 <= C^2 Re <(I - T P T†) y, y>.
```

Equivalently, the raw quotient must be bounded on the range of `W` and extend
to its closure.  The positive Gram identity removes ambiguity about the two
channels and prevents replacing the signed source estimate by separate
triangle inequalities.

## What remains open

The source still has to prove a finite constant `C`, uniformly in the visible
prime and suffix:

```text
exists C >= 0, forall y,
  ||R0 y||^2 <= C^2 ||W y||^2.
```

Injectivity of `W`, positivity of `W† W`, the signed coframe telescope, and
the residual operator-norm bounds do not imply this lower-bound comparison on
an infinite-dimensional global-log `L2` carrier.  No Gate 3U, finite-S sign,
Burnol identity, or RH theorem is claimed.

## Verification

The Windows source was synchronized to the Ubuntu-24.04 WSL2 ext4 mirror.

```text
lake build \
  ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
result: 3331 jobs, PASS
```

```text
focused audit: 3332 jobs, PASS
CCM25Concrete aggregate: 3843 jobs, PASS
full repository: 3924 jobs, PASS
```

The focused audit reports exactly `[propext, Classical.choice, Quot.sound]`
for the new declarations.  The WSL localhost-proxy notice and existing
repository linter warnings are environmental or pre-existing.  No `sorry`,
`admit`, or user axiom was added.
