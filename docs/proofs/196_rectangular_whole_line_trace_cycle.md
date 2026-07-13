# Proof 196: Unconditional compact-to-whole-line trace cycle

Status: accepted crossing-layer milestone. The source/global trace cycle,
named operator identities, and final Hilbert--Schmidt premise are formalized.
RH remains unproved.

## What is now proved

`PositiveTrace.lean` adds two general theorems.

`summable_adjoint_normSq` proves that if `T` is square summable on one source
Hilbert basis, then `T†` is square summable on every target Hilbert basis. The
proof exchanges the absolutely summable matrix coefficient series; it does
not assume basis independence.

`ordinaryTraceAlong_three_comp_eq_cycle` proves

```text
Tr_source(B X Y) = Tr_global(X Y B)
```

when both cuts through the factor space are Hilbert--Schmidt pairs. This avoids
the invalid shortcut of cycling a bounded operator against an operator known
only to be Hilbert--Schmidt.

## Crossing instantiation

On the reflected kernel interval `K*=[-c-b,-a+b]`, define

```text
B = globalL2ToSourceInterval,
X = C_g E_K*,
Y = leftKernel(g*)†.
```

The bridge proves the two operator identities

```text
(B X) Y = namedSourceCrossingProduct,
X (Y B) = cc20GlobalConvolutionCrossing g.involution.test b.
```

The second identity uses `T_b S†S=J_b` and the genuine convolution adjoint; it
does not commute `J_b` through convolution.

All four cycle premises are discharged:

```text
B X  is Hilbert--Schmidt: reflected right compact kernel,
Y    is Hilbert--Schmidt: adjoint of reflected left compact kernel,
Y B  is Hilbert--Schmidt: coisometry of S† plus adjoint basis transport.
X    is Hilbert--Schmidt: finite continuous-kernel factorization below.
```

## Final kernel-energy premise

Let

```text
K* = [-c-b,-a+b],
J  = [a-c-b,c-a+b].
```

The adjoint of `X=C_g E_K*` restricts to the finite operator

```text
A : L2(J) -> L2(K*),
A(y,t) = g(t-y).
```

`reflectedWholeLineAdjointFiniteOperator` constructs `A` with
`ContinuousKernelHilbertSchmidt`. Dense-core equality identifies
`A R_J = X†`; adjoint basis transport then proves
`reflectedWholeLineLeftFactor_summable`. No trace-class record or numerical
trace is stored.

Consequently `namedSource_trace_eq_globalConvolutionCrossing` and
`pairData_trace_eq_globalConvolutionCrossing` prove

```text
Tr_compact(pairData.traceProduct)
  = Tr_global(C_h C_(h*) J_b).
```

The remaining bottom is no longer a crossing trace conversion. It is the
same-object semilocal Euler-log variation, multi-prime assembly, remainder
control, and final sign gate.

## Verification

The source module builds in the isolated WSL verification copy with 2978
jobs. The focused import-facing audit builds with 2979 jobs. Every new
declaration reports only `propext`, `Classical.choice`, and `Quot.sound`.
