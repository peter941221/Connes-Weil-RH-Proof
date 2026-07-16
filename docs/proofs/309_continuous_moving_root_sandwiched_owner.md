# Proof 309: continuous moving root-sandwiched owner

Date: 2026-07-16

Status: closed for an abstract continuous finite-window time family.  The
named two-point scalar and its trace response are continuous and Bochner
integrable on `[0,1]`, with the explicit `-2` source residue kept inside the
same scalar.  This does not construct or identify the actual moving
`E_alpha/R_alpha/K_prol` source and does not prove Gate 3U.

## 1. What is closed

`MovingRootSandwiched.lean` defines the compact transport-time carrier and
its pulled-back Lebesgue measure:

```text
cc20MovingTime := Set.Icc (0 : R) 1

cc20MovingTimeMeasure
  := Measure.comap Subtype.val volume
```

The measure is registered as finite by computing its mass through the
measurable subtype embedding and `Real.volume_Icc`.  This is necessary because
the subtype does not inherit an ambient `volume` measure automatically.

For jointly continuous root and kernel families, the module defines

```text
cc20MovingRootSandwichedTwoPointScalar
cc20MovingRootSandwichedResponse
```

and proves the pointwise readback

```text
cc20MovingRootSandwichedResponse_eq_twoPointScalar
```

The scalar has the complete signed form

```text
regular two-point kernel pairing
  - 2 * integral_x conjugate(rightRoot(time,x)) * leftRoot(time,x).
```

The residue is not deleted, integrated separately, or estimated branchwise.

## 2. Analytic content

The new continuity theorems are

```text
continuous_cc20MovingRootSandwichedTwoPointScalar
continuous_cc20MovingRootSandwichedResponse
```

They use Mathlib's parameterized integral theorem three times: for the inner
kernel integral, the root residue, and the outer kernel integral.  Joint
continuity on compact spatial carriers therefore descends to continuity in
transport time.

The compact time carrier and finite pulled-back measure then give

```text
integrable_cc20MovingRootSandwichedTwoPointScalar
integrable_cc20MovingRootSandwichedResponse
```

The logical flow is

```text
+---------------------------+
| jointly continuous inputs |
+-------------+-------------+
              |
              v
+---------------------------+
| continuous two-point      |
| signed scalar on [0,1]    |
+-------------+-------------+
              |
              v
+---------------------------+
| finite pulled-back        |
| Lebesgue time measure     |
+-------------+-------------+
              |
              v
+---------------------------+
| Bochner integrable        |
| complete response         |
+---------------------------+
```

## 3. Verification evidence

The WSL2 ext4 verification build passed:

```text
lake build ConnesWeilRH.Source.CC20Concrete.MovingRootSandwiched \
           ConnesWeilRH.Dev.MovingRootSandwichedAudit

Build completed successfully (2972 jobs).
```

The aggregate entry point also passed:

```text
lake build ConnesWeilRH.Source.CC20Concrete

Build completed successfully (3535 jobs).
```

The import-facing audit reports only the standard Mathlib quotient axioms:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx` or project axiom appears in the new theorems.

## 4. What remains open

```text
+--------------------------------------------------------------+
| CLOSED                                                       |
|  finite-window continuous moving scalar                      |
|  continuity of the trace and two-point readbacks             |
|  time integrability on the pulled-back Lebesgue measure      |
|  explicit preservation of the -2 source residue              |
+--------------------------------------------------------------+
| OPEN                                                         |
|  actual E_alpha/R_alpha/K_prol source identification         |
|  construction of that jointly continuous/measurable family  |
|  Gate 3U uniform signed bound                                 |
|  finite-S semilocal sign                                     |
|  arithmetic same-object and negative-owner integration       |
|  Burnol all-zero identity                                    |
|  Riemann hypothesis                                          |
+--------------------------------------------------------------+
```

The next hard theorem must instantiate the abstract continuous maps with the
actual synchronized source kernels and prove that their complete signed scalar
is the route's moving outer/second-support/prolate response.  Only after that
same-object identification can a Gate 3U estimate be relevant.

Final route status:

```text
RH=UNPROVED
```
