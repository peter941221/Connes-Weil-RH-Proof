# 088 Compact Log Convolution Multiplicativity Pass

Date: 2026-07-12

## Evidence

The project already proves the exact multiplicative law needed by the new
owner:

```text
CC20YoshidaConvolution.laplaceAt_convolution

laplaceAt (f.convolution g) s
  = laplaceAt f s * laplaceAt g s
```

The proof is an explicit Fubini/integral-convolution argument using
`MeasureTheory.integral_convolution`, not an axiom or a stored conclusion.
The same file proves the convolution iterate power law
`laplaceAt_convolutionIterate`.

Combined with proof 087's raw log-pullback/Mellin identity, this establishes
the centered Xi/Mellin multiplicative coordinate after the parameter shift
`u=s-1/2`.

## Gate verdict

```text
genuine log convolution: pass
Laplace multiplicativity: pass
Mellin pullback: pass
centered orbit parameter: pass algebraically
source-owner API integration: open
```

The Plan 026 mathematical carrier is therefore no longer speculative. The
remaining work is to expose `CompactLogTest` (or an equivalent injective
carrier) to the route without the invalid full-Schwartz equivalence.

