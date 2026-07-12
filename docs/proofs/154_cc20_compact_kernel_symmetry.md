# CC20 compact regular-kernel symmetry

The compact real-coordinate kernel is now proved symmetric on the same
`[1/2,2] × [1/2,2]` domain:

```lean
cc20CompactRegularKernel (p.2, p.1) = cc20CompactRegularKernel p
```

The proof explicitly transports the compact subtype coordinates through the
`max(x,1/2)` positivity map and then applies the already proved symmetry of
the positive-coordinate ratio kernel. No symbol-only or `HEq` transport is
used.

This is a necessary condition for a self-adjoint kernel operator, but the
`L2` self-adjointness proof and the CC20 source `K_I` action identity remain
separate obligations.
