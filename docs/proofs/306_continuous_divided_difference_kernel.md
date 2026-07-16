# Proof 306: continuous divided-difference kernel

Date: 2026-07-16

Status: the removable-diagonal divided-difference witness is now formalized
and consumed by the root-sandwiched trace-class owner. The actual moving
`E/R/K_prol` same-object identity, the finite-`S` sign, and RH remain open.

## Core construction

For a multiplier `f` with a continuous derivative `f'`, define the quotient by
one segment average:

```text
D_f(s,t) = integral_0^1 f'(t + u (s-t)) du.
```

This is a continuous function of `(s,t)` on the whole plane. Its diagonal is
not a separate branch:

```text
D_f(t,t) = f'(t).
```

Mathlib's `intervalIntegral.integral_unitInterval_deriv_eq_sub` proves the
fundamental identity

```text
(s-t) * D_f(s,t) = f(s)-f(t),
```

and therefore, when `s != t`,

```text
D_f(s,t) = (f(s)-f(t))/(s-t).
```

The quantized kernel is then

```text
Q_f(s,t) = i/pi * D_f(s,t).
```

The source-facing data contract is:

```text
CC20DividedDifferenceData
  value      : ContinuousMap R C
  derivative : ContinuousMap R C
  hasDerivAt : forall x, HasDerivAt value (derivative x) x
```

A quotient formula without the derivative proof cannot instantiate this
contract.

For the route's test-function class,
`cc20DividedDifferenceDataOfSchwartz` builds the contract directly from a
`SchwartzMap ℝ ℂ`, using Mathlib's `SchwartzMap.derivCLM`. No hand-written
derivative-continuity premise is needed for that class.

## Lean owner

The implementation is
`ConnesWeilRH/Source/CC20Concrete/DividedDifferenceKernel.lean`:

```text
cc20DividedDifferenceDataOfSchwartz
cc20SegmentAverageDerivative
cc20SegmentAverageDerivative_diag
cc20SegmentAverageDerivative_smul_eq_sub
cc20SegmentAverageDerivative_eq_dividedDifference
cc20QuantizedDividedDifferenceKernel
cc20QuantizedDividedDifferenceKernel_diag
cc20QuantizedDividedDifferenceKernel_offDiagonal
cc20WindowQuantizedDividedDifferenceKernel
cc20WindowQuantizedDividedDifferenceKernel_diag
cc20WindowQuantizedDividedDifferenceKernel_offDiagonal
cc20WindowRootSandwichedDividedDifferencePairData
cc20WindowRootSandwichedDividedDifferencePairData_traceProduct_isTraceClass
cc20WindowRootSandwichedDividedDifferenceResponse
```

The last pair-data theorem delegates only to the already-proved continuous
kernel `A†B` theorem. It does not smuggle in a moving projection identity or a
trace of an unsmoothed translated projection.

The dependency chain is now:

```text
HasDerivAt + continuous derivative
              |
              v
segment-average continuous kernel
              |
              v
CC20 off-diagonal divided difference + exact diagonal value
              |
              v
root-sandwiched A†B trace class
              |
              +---- explicit -2 root pairing
```

## Verification

The import audit is
`ConnesWeilRH/Dev/DividedDifferenceKernelAudit.lean`. In the isolated WSL2
mirror:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Source.CC20Concrete.DividedDifferenceKernel

flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Dev.DividedDifferenceKernelAudit \
             ConnesWeilRH.Source.CC20Concrete
```

The audited declarations use only:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx`, no new project axiom, and no hidden regularity premise.
The full default target passes with `3587` jobs. All `99` probe files parse,
and the `28` probes from Proofs 278--306 exit successfully with
`RH=UNPROVED`.

The finite guard is
`docs/proofs/306_continuous_divided_difference_probe.py`:

```text
cohort                 offdiag      diagonal      normalization
default                1.30e-15     2.22e-16      4.17e-16
alternate              2.19e-15     1.67e-16      6.97e-16
```

Both cohorts have zero constant-mode kernel, machine-precision root-trace
readback, a nonzero residue omission gap, and print `RH=UNPROVED`.

The source normalization is CC20 Appendix D/E, arXiv:2006.13771:

```text
https://arxiv.org/abs/2006.13771
```

## What remains hard

This proof closes the local kernel regularity and trace-class interface, not
the route's arithmetic endpoint. The next identity must identify the same
root-paired scalar with all moving branches:

```text
root-sandwiched Q_f response
  = moving outer E/R response
      + second-support branch
      + K_prol branch
      - 2 root inner product.
```

Only after that identity can compact root support be used before the single
absolute value in the `S`-uniform estimate. Gate 3U, the finite-`S` sign,
Burnol's identity, and RH remain unproved.
