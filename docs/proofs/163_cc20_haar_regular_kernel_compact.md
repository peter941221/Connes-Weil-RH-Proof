# CC20 Haar Regular-Kernel Compactness

Date: 2026-07-12

## Result

`RegularKernelHaarCompact.lean` proves that the ordinary CC20 regular-kernel
operator on the source Haar space is compact:

```text
isCompactOperator_cc20CompactHaarComplexL2Operator
exists_finiteDimensional_cc20HaarRegularRemainder_nonpositive
```

The proof constructs the bounded-continuous coefficient image of the Haar-L2
unit ball, proves pointwise boundedness and equicontinuity from the same
continuous kernel sections, applies Arzela--Ascoli, and transports the compact
image through `BoundedContinuousFunction.toLp`.

The second theorem instantiates `CompactBadSpace` at threshold `2`: outside a
finite-dimensional control space, the real quadratic form of
`K_I - 2 Id` is nonpositive.

## Verification

```text
lake build ConnesWeilRH.Source.CC20Concrete.RegularKernelHaarCompact
lake env lean ConnesWeilRH/Dev/RegularKernelSourceBridgeAudit.lean
```

Both pass in the WSL2 mirror with the existing `.lake` cache. The focused
axiom audit remains limited to `propext`, `Classical.choice`, and `Quot.sound`.

## Boundary

This proves compactness of the ordinary regular kernel only. The independent
diagonal `-2 Dirac_0` contribution, the full `-2 Id + K_I` quadratic-form
identity, and the arithmetic/pole/archimedean same-test read-off remain open.
