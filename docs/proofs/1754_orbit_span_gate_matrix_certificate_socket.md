# 1754 — Orbit span gate/matrix certificate socket

Date: 2026-09-21

## Result

The active healthy-`CompactLog` B5 producer now has an exact finite-span
certificate interface. For a finite real span `spanObj w y`, under the named
window-support and pairwise archimedean-integrability hypotheses,
`orbitWindowSemiLocalGate (spanObj w y)` is equivalent to the nonpositivity of
the finite gate-matrix quadratic form `y ⬝ᵥ (gateMatrix w *ᵥ y)`.

The Lean declaration is
`C1P2SpanProfileMatrix.orbitWindowSemiLocalGate_spanObj_iff_gate_qform_nonpos`.
Its proof rewrites the orbit gate to `p2AggregateValue`, then uses the existing
exact span-to-matrix identity. No positivity assumption, numerical claim, or
RH conclusion is introduced.

## Verification

`C1P2SpanProfileMatrix` and its paired Audit target built successfully in
`shortest_route_20260921_span_gate_v4.log` (3784 jobs), with zero `error:` lines
and zero `sorryAx`. The focused audit prints exactly
`[propext, Classical.choice, Quot.sound]` for both declarations.

## Remaining obligation

The producer still has to construct the same selected OrbitG8 owner as a
finite span with admissible support/integrability data and prove the resulting
`-gateMatrix` semidefinite certificate. This record is a formal interface and
does not claim that either obligation has been discharged.
