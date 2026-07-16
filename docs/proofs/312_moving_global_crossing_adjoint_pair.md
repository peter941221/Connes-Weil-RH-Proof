# Proof 312: moving global crossing adjoint pair

Date: 2026-07-16

Status: closed for the genuine forward/adjoint outer-crossing pair.  The
reverse response is owned by the Hilbert-space adjoint of the existing global
crossing operator.  It is not a second copy of the forward scalar and it is
not an abstract kernel assumption.

This does not construct the second-support projection, the Sonin projection
`R`, or the prolate correction `K_prol`.

## 1. What the new owner is

Proof 311 used the concrete whole-line operator

```text
C_b = P_negative Translation_b P_positive.
```

Proof 312 adds its genuine adjoint `C_b^dagger` and defines

```text
forward(a) = inner(h_a, C_(b(a)) h_a),
reverse(a) = inner(h_a, C_(b(a))^dagger h_a),
pair(a)    = forward(a) + reverse(a).
```

The adjoint identity gives

```text
reverse(a) = conjugate(forward(a)).
```

Consequently the pair is Hermitian (real-valued):

```text
pair(a) = 2 * Re(forward(a)),
Im(pair(a)) = 0.
```

## 2. Exact reverse boundary readback

For `b(a) >= 0`, Proof 311 proved

```text
forward(a)
  = integral_(-b(a))^0 conjugate(h_a(t)) h_a(t+b(a)) dt.
```

Complex conjugation commutes with the Bochner integral.  Therefore the actual
adjoint response is

```text
reverse(a)
  = integral_(-b(a))^0 conjugate(h_a(t+b(a))) h_a(t) dt.
```

The combined owner is read back before any norm or absolute value:

```text
pair(a)
  = integral_(-b(a))^0
      [conjugate(h_a(t)) h_a(t+b(a))
       + conjugate(h_a(t+b(a))) h_a(t)] dt.
```

This ordering matters.  Estimating the two branches separately would discard
the conjugate cancellation that makes the pair real.

## 3. Continuity and time integration

The reverse response is the conjugate of Proof 311's continuous forward
response, so it is continuous without an operator-norm continuity assumption
on translated half-line projections.  Compactness of `cc20MovingTime` and the
finite pulled-back measure `cc20MovingTimeMeasure` then give Bochner
integrability of both the reverse branch and the combined pair.

The theorem

```text
integral_cc20MovingSingleCrossingPairResponse_eq_boundaryIntegral
```

keeps the pair combined under the time integral.

## 4. Lean declarations

`MovingGlobalCrossingPair.lean` provides

```text
cc20MovingSingleCrossingAdjointResponse
cc20MovingSingleCrossingAdjointBoundaryIntegrand
cc20MovingSingleCrossingAdjointResponse_eq_star
cc20MovingSingleCrossingAdjointResponse_eq_boundaryIntegral
continuous_cc20MovingSingleCrossingAdjointResponse
integrable_cc20MovingSingleCrossingAdjointResponse
cc20MovingSingleCrossingPairResponse
cc20MovingSingleCrossingPairResponse_eq_two_re
cc20MovingSingleCrossingPairResponse_im
cc20MovingSingleCrossingPairResponse_eq_boundaryIntegral
continuous_cc20MovingSingleCrossingPairResponse
integrable_cc20MovingSingleCrossingPairResponse
integral_cc20MovingSingleCrossingPairResponse_eq_boundaryIntegral
```

## 5. Verification

Focused WSL2 ext4 build:

```text
lake build ConnesWeilRH.Source.CC20Concrete.MovingGlobalCrossingPair \
           ConnesWeilRH.Dev.MovingGlobalCrossingPairAudit

Build completed successfully (2978 jobs).
```

Aggregate build:

```text
lake build ConnesWeilRH.Source.CC20Concrete

Build completed successfully (3538 jobs).
```

The audited declarations depend only on

```text
[propext, Classical.choice, Quot.sound]
```

and introduce no `sorryAx` or project axiom.

## 6. Honest route boundary

```text
+--------------------------------------------------------------+
| CLOSED                                                       |
|  genuine moving C_b and C_b^dagger outer responses           |
|  exact forward and reverse finite-boundary readbacks         |
|  Hermitian pair assembled before any estimate                |
|  continuity, integrability, and time-integrated readback     |
+--------------------------------------------------------------+
| OPEN                                                         |
|  actual second-support projection and crossing               |
|  actual Sonin R and K_prol producers                         |
|  same-object outer-minus-Sonin-prolate recombination         |
|  identification with the root-sandwiched owner and -2 term   |
|  Gate 3U, finite-S sign, Burnol identity, and RH             |
+--------------------------------------------------------------+
```

The next source-level bottleneck is not another abstract continuity wrapper.
It is a genuine second-support/Sonin producer that can be recombined with this
outer pair and the prolate correction on the same object.

Final route status:

```text
RH=UNPROVED
```
