# 1051 - C1 metric-projection prime-square guard

Date: 2026-08-29.

Status: conditional NO-GO diagnostic for direct Euler-log readback from the
current C1 endpoint Gram-projection response beyond first prime powers. The
identity of the active response is Lean-checked. The factor-two conclusion
additionally requires the source-Sonin principal channel to survive as the
same nonzero detector-trace channel as the radial Euler crossing; that bridge
is not yet formalized. Proof 1052 independently gives the unconditional Lean
no-go for the current canonical-cutoff closure of the positive
projection-square route.

## 1. What Is Being Tested

The active C1 response is not merely similar to the earlier metric-Sonin
candidate. It is that candidate on the common carrier.

```text
T_p = I - a U,                 a = p^(-1/2),  U = translation by log p
R_0 = source Sonin projection
R_p = projection onto T_p Ran(R_0), with the induced L2 metric

projectionResponse = detector (R_0 - R_p).
```

The code-level identifications are direct:

```text
CCM24EulerTransport.lean:49-90
  T_p = I - p^(-1/2) U_(-log p)

GramCorrectedSoninTransport.lean:36-40, 285-288
  projection onto a transported range = A (A^* A)^(-1) A^*

CCM24SoninProjectionBridge.lean:71-73
  gramCorrectedTargetSoninProjection = transportedSoninStarProjection

C1Stage3ProjectionTraceLedger.lean:76-79, 94-97
  soninBandDifference = R_0 - R_p
  projectionResponse = detector o soninBandDifference.
```

`C1MetricProjectionResponseGuard.lean` makes the last equality an audited
Lean theorem without introducing any new analytic premise.

## Verification

The focused WSL2 build was

```text
lake build ConnesWeilRH.Dev.C1MetricProjectionResponseGuard \
  ConnesWeilRH.Dev.C1MetricProjectionResponseGuardAudit
```

It ended with `Build completed successfully (3161 jobs)`. Both declarations
print exactly `[propext, Classical.choice, Quot.sound]`; neither uses
`sorryAx`.

## 2. Conditional One-Prime Principal-Channel Calculation

Put `Q = I - R_0`, `V = U + U^*`, and let `C_f` be the same commuting
convolution-square detector used by the response. The Gram metric is

```text
H_a = T_p^* T_p = I - a V + a^2 I,
A_a = R_0 H_a R_0 = (1 + a^2) R_0 - a R_0 V R_0.
```

The target orthogonal projection is

```text
R_p = T_p R_0 A_a^(-1) R_0 T_p^*.
```

Using trace cyclicity only after the standard CC20 smoothing, the finite-place
part of the endpoint response is

```text
-a Tr(R_0 C_f Q V R_0 A_a^(-1)).                       (G.1)
```

For `a` near zero,

```text
A_a^(-1)
 = R_0 + a R_0 V R_0
     + a^2 ((R_0 V R_0)^2 - R_0) + O(a^3).
```

Therefore its first two coefficients are

```text
-a   Tr(R_0 C_f Q V R_0)
-a^2 Tr(R_0 C_f Q V R_0 V R_0).                         (G.2)
```

For the second coefficient, insert `R_0 = I - Q` into the internal factor:

```text
Q V R_0 V R_0 = Q V^2 R_0 - Q V Q V R_0.
```

The second term has two boundary crossings. The one-crossing principal term is

```text
Q V^2 R_0 = Q (U^2 + U^(*2)) R_0,
```

because `Q R_0 = 0`. Its coefficient is exactly `a^2`, not `a^2 / 2`.

## 3. The Prime-Square Contradiction, Conditional On That Channel

The Euler logarithm required by the selected crossing readback is

```text
-log(I - a U) = sum_(m >= 1) a^m U^m / m.
```

At `m = 2`, the required one-crossing coefficient is `a^2 / 2`. A crossing by
`U^m` has length `m log p`, so the two trace contributions are

```text
endpoint metric projection:
  a^2 * 2 log p * (F(2 log p) + F(-2 log p))

Weil p^2 atom:
  (a^2 / 2) * 2 log p * (F(2 log p) + F(-2 log p)).
```

The endpoint owner is twice the Weil coefficient. Reversing the global sign
convention reverses both expressions and does not remove the factor two.

The excess is the one-crossing partial translation `Q U^2 R_0` (and its
adjoint). If the source-Sonin principal-channel bridge identifies it with the
nonzero selected radial `p^2` channel, then it has infinite rank before
smoothing and cannot be hidden in a remainder declared negligible by
compactness or by a multi-crossing ideal. The current Lean code proves the
response identity but does not yet prove that principal-channel bridge.

This is the same calculation recorded in proof 042. The new point here is the
exact identification of its rejected object with the active C1 response.

## 4. Why The Positive Kernel Does Not Escape

The C1 positive kernel is

```text
K_p = E Q_p E - R_p.
```

Its window bridge rewrites the positive trace through the same endpoint
response plus two defects. The second defect cannot tend to zero for a nonzero
test: `C1Stage3ProjectionDefectBounds.lean:506` proves precisely that result.
Thus retaining the positive kernel does not repair the metric coefficient; it
adds a separate non-vanishing finite-part obligation.

The exact decomposition in
`C1SelectedDetectorSemiLocalResidualDecomposition.lean:80-100` is useful
bookkeeping,

```text
R_0 - R_p = (K_p - K_0) - E(Q_p - Q_0)E,
```

but it is an identity, not an additional one-crossing channel. Recombining the
two right-hand terms returns the rejected endpoint metric response.

## 5. Scope Of The Conditional Diagnostic

```text
conditionally rejected once the stated principal-channel bridge is proved:
  current C1 metric endpoint response as a full Euler-log trace owner;
  a residual-to-zero/compactness proof for that response when p^2 is visible;
  treating the K_p decomposition as a repair of the factor-two error.

not rejected:
  the local CC20 ROOT theorem;
  first-power-only tests for which every p^2 atom vanishes by support;
  a future semilocal owner that derives the logarithm before projection
  normalization and proves a new positivity theorem for that owner.
```

The first-power exception cannot by itself establish the detector-selected RH
step: the intended detector family has no established global support bound that
excludes every visible `p^2` atom.

## 6. Consequence

Proof 1052 already rules out a `windowToResponseDefect -> 0` repair for the
canonical cutoff, with no principal-symbol premise. A future semilocal attempt
must therefore begin with a different finite-part owner, not another estimate
on that defect. If it seeks direct Euler readback, it must contain the Euler
logarithm `a^m/m` before the translation crossing supplies `m log p`, and it
must independently establish one positive same-owner trace. Standard
alternatives already screened in this repository do not supply that
combination:

```text
raw/regularized Fredholm determinant: trace-ideal failure (proof 119)
positive log-Poisson factorization: loses linear readback (proof 111)
orthogonal graph projection: p^3 contamination (proof 128)
inverse-log metric projection: one-crossing leak (proof 205/206)
```

Primary source boundary:

```text
Connes--Consani--Moscovici, Zeta zeros and prolate wave operators,
https://arxiv.org/html/2310.18423

Connes--Consani, Weil positivity and Trace formula, the archimedean place,
https://arxiv.org/html/2006.13771
```
