# Proof 311: concrete moving global crossing

Date: 2026-07-16

Status: closed for one genuine moving outer-crossing branch.  The response is
defined from the existing whole-line half-line projection and translation
operator, not from an arbitrary continuous kernel.  A continuous nonnegative
boundary shift and continuous Schwartz path give an exact moving boundary
integral, a continuous scalar response, and a Bochner-integrable time family.

This does not yet construct the Sonin `R` projection, the second-support
branch, or the prolate correction `K_prol`.

## 1. Actual operator owner

The existing source operator is

```text
cc20SingleCrossingOperator b
  = P_negative * Translation_b * P_positive
```

on the whole-line logarithmic Hilbert space `L2(R)`.  Proof 311 defines

```text
cc20MovingSingleCrossingResponse boundaryShift testPath a
  = inner(testPath(a),
      cc20SingleCrossingOperator(boundaryShift(a)) testPath(a)).
```

The same Schwartz test is used on both sides.  This matches the diagonal-first
route required before complex polarization; unrelated `L2` witnesses are not
mixed.

## 2. Moving boundary readback

For `b(a) >= 0`, the concrete crossing is supported on the finite interval
`[-b(a),0]`.  The exact readback is

```text
inner(h_a, C_(b(a)) h_a)
  = integral_(-b(a))^0 conjugate(h_a(t)) h_a(t+b(a)) dt.
```

The implementation uses the existing theorem

```text
cc20SingleCrossingOperator_schwartz_inner_eq_boundary_integral
```

and converts the set integral on `Icc (-b,0)` to the oriented interval
integral through `integral_Icc_eq_integral_Ioc` and
`intervalIntegral.integral_of_le`.

## 3. Why continuity is legal

No operator-norm continuity of `b -> cc20SingleCrossingOperator b` is assumed.
The proof moves to the explicit scalar boundary integral first.  For

```text
f(a,t)=conjugate(h_a(t))*h_a(t+b(a)),
```

joint continuity follows from the Schwartz inclusion into bounded continuous
functions.  The variable interval is handled as

```text
integral_(-b(a))^0 f(a,t) dt
  = - integral_0^(-b(a)) f(a,t) dt,
```

then Mathlib's

```text
intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
```

proves continuity in `a`.  Compact time and the finite pulled-back Lebesgue
measure from Proof 309 then give Bochner integrability.

## 4. Lean declarations

`MovingGlobalCrossing.lean` provides

```text
cc20MovingSingleCrossingResponse
cc20MovingSingleCrossingBoundaryIntegrand
cc20MovingSingleCrossingResponse_eq_boundaryIntegral
continuous_cc20MovingSingleCrossingResponse
integrable_cc20MovingSingleCrossingResponse
integral_cc20MovingSingleCrossingResponse_eq_boundaryIntegral
```

The final theorem keeps the actual operator response and its explicit boundary
integral under the same time measure.

## 5. Verification

Focused WSL2 ext4 build:

```text
lake build ConnesWeilRH.Source.CC20Concrete.MovingGlobalCrossing \
           ConnesWeilRH.Dev.MovingGlobalCrossingAudit

Build completed successfully (2977 jobs).
```

Aggregate build:

```text
lake build ConnesWeilRH.Source.CC20Concrete

Build completed successfully (3537 jobs).
```

The new declarations depend only on

```text
[propext, Classical.choice, Quot.sound]
```

and introduce no `sorryAx` or project axiom.

## 6. Honest route boundary

```text
+--------------------------------------------------------------+
| CLOSED                                                       |
|  concrete P_negative Translation_b P_positive operator      |
|  moving diagonal Schwartz response                           |
|  exact finite moving boundary integral                       |
|  continuity and time integrability                           |
+--------------------------------------------------------------+
| OPEN                                                         |
|  reverse/adjoint crossing branch                             |
|  actual second-support projection                            |
|  actual Sonin R and K_prol producers                         |
|  complete outer-minus-Sonin-prolate same-object identity     |
|  Gate 3U, finite-S sign, Burnol identity, and RH             |
+--------------------------------------------------------------+
```

Proof 311 is the first Proof 309 successor whose scalar is owned directly by
an existing global source operator.  It closes one branch only.  Branchwise
absolute estimates remain forbidden: the next relevant owner must recombine
the outer, second-support, and prolate responses before taking one absolute
value.

Final route status:

```text
RH=UNPROVED
```
