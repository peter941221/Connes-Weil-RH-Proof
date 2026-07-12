# CC20 Haar Kernel Symmetry

Date: 2026-07-12

## Result

`RegularKernelHaarSymmetry.lean` proves the same regular kernel is symmetric on
the actual source Haar space:

```text
cc20CompactHaarComplexL2Operator_inner_symmetry
```

The proof first establishes the compact Haar-product bilinear integrability,
uses the real symmetric kernel and Fubini, then extends the identity from
continuous inputs to all complex `L2` inputs by the dense range of
`ContinuousMap.toLp`.

## Verification

```text
lake build ConnesWeilRH.Source.CC20Concrete.RegularKernelHaarSymmetry
lake env lean ConnesWeilRH/Dev/RegularKernelSourceBridgeAudit.lean
```

Both pass in the WSL2 mirror reusing the existing `.lake` cache. The focused
axiom audit for the new theorem remains limited to `propext`,
`Classical.choice`, and `Quot.sound`.

## Boundary

This proves symmetry of the ordinary regular kernel only. It does not include
the separate diagonal Dirac contribution, prove the CC20 `-2 Id + K_I`
quadratic-form identity, or establish the finite-prime/pole read-off needed by
the RH route.
