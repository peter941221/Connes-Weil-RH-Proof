# 012 — G8 same-owner readback: compressed reachability audit

Status: conditional fallback architecture. The logical corridor is formal;
the decisive operator-energy estimates are open. Generic work on this lane is
frozen by the core-progress gate.

## Logical spine

On the same healthy `CompactLog` owner, the G8 program was designed to prove:

```text
finite metric cutoffs
  -> diagonal energy / trace-class control
  -> cutoff and endpoint trace limits
  -> readback of the actual selected detector
  -> qw(g) >= 0
  -> contradiction with the formal qw(g) < 0
```

The selected detector and negative sign are formal in
`C1HealthyYoshidaSpectralNegativity.lean`. Conditional trace/readback and
contradiction consumers exist in the G8/R3 modules. They do not supply the
open energy hypotheses.

## Exact remaining analytic objects

Use the notation from [042]:

```text
C = rootConvolution(owner)
J = sourceInclusion(scale)
P = sourceSoninProjection(scale)
```

The survivor obligation has been reduced to the source-compressed square-sum

```text
sum_i ||J† C J e_i||^2 < infinity,
```

equivalently the projected-root form after the established source/prolate
normal forms. The finite source-side Schur factor is a unit and therefore does
not create the missing decay.

The visible-boundary obligation has a finite family of analogous composite
terms. Its radial-boundary part is formal for the actual physical columns; the
internal-gap/commutator-root square-sum remains open.

## What is already formal

- actual orbit geometry and finite visible-prime families;
- finite-stage weighted/trace legality infrastructure;
- no-gap alternating-power convergence to the intersection projection;
- survivor and boundary coframe factorizations;
- endpoint-limit conditionals and cutoff/readback reductions;
- range/prolate pieces and several exact normal forms;
- the contradiction consumer, conditional on the missing energy/readback.

Representative modules include `C1G8R0OrbitGeometry.lean`,
`C1G8R3SurvivorCoframeBridge.lean`,
`C1G8R3BoundaryOutputFactorizationBridge.lean`,
`C1G8R3ActualEndpointTraceLimit.lean`, and `C1G8P3Contradiction.lean`.

## Hard guards

- The ambient leakage and ambient band-root operators are formally not
  Hilbert–Schmidt when the selected Laplace value is nonzero. Compression by
  the source/Sonin projection is essential.
- A fixed-window Hilbert–Schmidt bound grows with the window and does not give
  the required uniform annular trace bound.
- The old source-prolate pullback used by a boundary shortcut is zero; it
  cannot carry the desired energy.
- Hilbert–Schmidt membership alone does not provide the trace-class statement
  required by the final trace consumer.
- No bound may assume a `qw` sign, `SourceRH`, RH, or universal gate
  positivity.

## Reachability verdict

The route is logically capable of reaching the healthy B5 contradiction if
the source-compressed survivor energy and composite boundary energy are
proved on the actual detector owner. It is not currently the preferred
producer because those estimates have resisted reduction and the direct C3'
and phase-balanced lanes expose smaller scalar obligations.

The detailed operator split, current work orders, and precise no-go evidence
are retained in [042](042_g8_diagonal_leg_operator_bridge_audit.md). Historical
per-brick records 013--041 were removed from the map; their Lean declarations
and proof records remain authoritative.
