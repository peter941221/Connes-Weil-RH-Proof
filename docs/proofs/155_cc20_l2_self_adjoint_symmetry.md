# CC20 compact-kernel L2 symmetry

The compact kernel's exchange symmetry is now lifted to the integral operator.
For continuous inputs, compactness gives integrability of the bilinear kernel
on the product measure, and `integral_integral_swap` proves the double-integral
identity. `ContinuousMap.inner_toLp` then gives the corresponding `L2` inner
product identity on the dense continuous subspace.

Finally, `DenseRange.induction_on₂` extends the identity to all
`Lp ℝ 2 cc20CompactMeasure` inputs:

```lean
inner ℝ (cc20CompactL2Operator u) v
  = inner ℝ u (cc20CompactL2Operator v)
```

This proves the operator is symmetric/self-adjoint at the Hilbert-space inner
product level. It still does not prove Hilbert--Schmidt membership, identify
the operator with CC20's source `K_I`, or provide the trace/read-off identity.
