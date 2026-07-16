# Proof 310: moving divided-difference source owner

Date: 2026-07-16

Status: closed for the continuous divided-difference source family.  A
continuous path in Schwartz space now produces a jointly continuous value and
derivative family, whose segment-average quotient is fed into Proof 309's
moving root-sandwiched response.  This is a genuine source-kernel producer;
it is still not the actual `E_alpha/R_alpha/K_prol` projection owner.

## 1. Source producer

`MovingDividedDifferenceKernel.lean` defines

```text
CC20MovingDividedDifferenceData
  value      : ContinuousMap ([0,1] x R) C
  derivative : ContinuousMap ([0,1] x R) C
  hasDerivAt : pointwise real derivative proof
```

The direct producer is

```text
cc20MovingDividedDifferenceDataOfSchwartzPath
  : ContinuousMap cc20MovingTime (SchwartzMap R C)
    -> CC20MovingDividedDifferenceData.
```

It uses Mathlib's continuous linear maps

```text
SchwartzMap.toBoundedContinuousFunctionCLM
SchwartzMap.derivCLM
```

so joint continuity is inherited from the Schwartz path.  No hand-written
continuity premise for the derivative family is needed.  The constructor's
static slice is exactly the existing Proof 306 witness:

```text
(cc20MovingDividedDifferenceDataOfSchwartzPath path).at a
  = cc20DividedDifferenceDataOfSchwartz (path a).
```

There is also a `stationary` constructor from any static
`CC20DividedDifferenceData`, giving a nonempty producer even before a dynamic
source path is supplied.

## 2. Exact moving kernel

For a moving derivative `d(a,x)`, the removable diagonal is one continuous
object:

```text
D(a,s,t) = integral_0^1 d(a, t + u * (s - t)) du.
```

The module proves

```text
D(a,t,t) = d(a,t)
(s-t) * D(a,s,t) = value(a,s) - value(a,t)
D(a,s,t) = (value(a,s)-value(a,t))/(s-t),  s != t.
```

The normalized source kernel is

```text
Q(a,s,t) = i/pi * D(a,s,t),
```

and `cc20MovingWindowQuantizedDividedDifferenceKernel` restricts it jointly to
transport time and the finite CC20 Haar window.

## 3. Moving response owner

The source kernel is now consumed directly by the Proof 309 response:

```text
cc20MovingRootSandwichedDividedDifferenceResponse
```

The following theorems are available:

```text
cc20MovingRootSandwichedDividedDifferenceResponse_eq_static
continuous_cc20MovingRootSandwichedDividedDifferenceResponse
integrable_cc20MovingRootSandwichedDividedDifferenceResponse
cc20MovingRootSandwichedDividedDifferenceResponse_eq_twoPoint
integral_cc20MovingRootSandwichedDividedDifferenceResponse_eq_twoPoint
```

The signed scalar remains

```text
regular root-weighted two-point pairing
  - 2 * inner(rightRoot, leftRoot).
```

The residue is kept in the same integrand.  No diagonal Dirac term is silently
inserted into the continuous kernel, and no branchwise absolute value is taken.

## 4. Verification

Focused WSL2 ext4 verification:

```text
lake build ConnesWeilRH.Source.CC20Concrete.MovingDividedDifferenceKernel \
           ConnesWeilRH.Dev.MovingDividedDifferenceKernelAudit

Build completed successfully (2974 jobs).
```

Aggregate verification:

```text
lake build ConnesWeilRH.Source.CC20Concrete

Build completed successfully (3536 jobs).
```

The audit reports only

```text
[propext, Classical.choice, Quot.sound]
```

for the new declarations.  No `sorryAx` or project axiom is introduced.

## 5. Honest boundary

```text
+--------------------------------------------------------------+
| CLOSED                                                       |
|  Schwartz-path source producer                               |
|  moving divided-difference diagonal and quotient             |
|  finite-window kernel restriction                            |
|  static slice / moving response equality                     |
|  continuity, integrability, and signed time readback         |
+--------------------------------------------------------------+
| OPEN                                                         |
|  actual E_alpha/R_alpha/K_prol projections and kernels       |
|  moving Hardy/Sonin/prolate same-object identity             |
|  arithmetic finite-prime trace identification                |
|  Gate 3U uniform signed estimate                             |
|  finite-S sign, Burnol identity, and RH                      |
+--------------------------------------------------------------+
```

Proof 310 removes the generic-kernel-family gap from the divided-difference
lane.  It does not turn a Schwartz path into the semilocal projection geometry
required by the RH route.  The next theorem must identify the actual moving
three-branch source response with this source kernel under the same root
pairing, including the explicit `-2` residue.

Final route status:

```text
RH=UNPROVED
```
