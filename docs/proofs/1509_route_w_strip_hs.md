# 1509 — Route W compressed strip Hilbert–Schmidt lemma (WO-B3, 1503 §3)

**Status: FORMAL, GREEN first content try.** `C1G8R3RouteWStripHilbertSchmidt.lean`
(+ paired Audit) lands the analytic Route W window-strip ingredient.
Acceptance: `build-logs/0916_route_w_strip_try2.log`, 3213 jobs, zero
`error:` lines, both audited declarations print
`[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.

## What is proved

For an ARBITRARY bounded window — parameters `(A, C, d, e)` free — the
compressed window-strip operator

```text
routeWCompressedStripOperator owner A C d e
  = kernelIntervalL2ZeroExtension d e 0
      ∘L kernelOperator(compactOutputRootKernel owner.sourceTest A C d e)
      ∘L (globalL2ToKernelInterval (d+A) (e+C) 0 ∘L cc20PositiveHalfLineProjection)
```

has square-summable columns on any named ambient basis
(`routeWCompressedStripOperator_basis_normSq_summable`), and the
P-post-composed version — the `P C P_W` of route W — keeps the square-sum
(`routeW_compressedStrip_projection_basis_normSq_summable`).

This is the general-window version of the record-1495/1496 finite-window
mechanism: the window can be placed anywhere on the log line and, in
particular, grown (`W_N`), which is exactly the freedom route W's
window/tail split (record 1505) consumes. The kernel is continuous on the
compact strip `W × (W + supp)`, so the strip is Hilbert–Schmidt with no
two-sided-condition input.

## Scope

The TAIL composition is not estimated here. Per record 1505 the tail gate
is the minimal irreducible remainder of route W, and per the record-1503
Hardy-pressure finding any estimate of it must read the phase of the
scattering multiplier; that remains the open mathematics. The G8 gate,
ρ4/ρ5, C3, and RH remain open. RH not claimed.
