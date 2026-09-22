# 1850 - Fixed-correction all-index assembly

Date: 2026-09-22.

Status: Formally verified in Lean 4; producer-side interface progress only.

Module: `ConnesWeilRH.Source.CC20YoshidaConvolution`.

The theorem `exists_nearbyZero_unscaled_targetValues_assembly_with_fixedCorrection`
changes the quantifier order of the unscaled assembly layer. For each nearby
zero radius it first chooses one correction and one nonnegative quadratic
constant `C`. It then exposes, for every natural convolution count `n`, the
support inclusion, target interpolation, selected-node zero equations, and the
explicit bound

```text
||z - rho||^2 * |Laplace(assembled_n, z)|
  <= (6*pi)^2 * ((1/2)^(n+1) * C).
```

The proof reuses `convolutionIterate_convolution_distance_quadratic_bound`;
the base transform equals one on target nodes, so changing `n` preserves the
target values. This is the missing quantifier shape needed to choose `n` from
the geometric budget after the correction constant is known.

This does not prove the orbit geometry producer, strict base contraction, or
detector-specific semi-local positivity. It is a formal interface brick only.

Verification: focused Lake build log `1850_fixed_correction.log`, zero
`error:` lines, and successful build footer; paired import-facing Audit now
prints the declaration and its axioms.
