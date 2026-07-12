# CC20 Compact Rectangle L2 Gate

Date: 2026-07-12

The concrete verification domain is

```text
sqrt(I) = [1/2, 2],     I = [1/4, 4]
sqrt(I) x sqrt(I)
```

inside the positive-coordinate subtype. The coordinate map
`x |-> <max x (1/2), positivity>` realizes this interval while preserving the
standard real coordinates on the rectangle.

The source theorem
`continuousOn_cc20RegularKernel_sqrtIRectangle` composes the scalar continuity
on `Ici 1` with `ratioRadius`, whose image is always in `Ici 1`. Mathlib's
The open positive subtype has no canonical `volume` instance. Therefore the
L2 theorem is stated in the real coordinates with standard product volume.
Mathlib's `ContinuousOn.integrableOn_compact` proves

```text
IntegrableOn (fun p => ||cc20RegularKernelReal p||^2)
  cc20RealSqrtIRectangle volume
```

in `integrableOn_cc20RegularKernelReal_sq_sqrtIRectangle`.

This establishes only the ordinary regular-kernel L2 gate. It does not prove
that the integral operator has the CC20 source action, that the operator is
the same object used by the trace formula, or that the resulting route proves
RH.
