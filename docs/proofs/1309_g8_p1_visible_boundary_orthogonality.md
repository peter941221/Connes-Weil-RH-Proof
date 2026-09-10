# G8 P1 visible-boundary orthogonality (2026-09-11)

The aggregate survivor orthogonality transports through the actual metric
visible-boundary coframe:

```text
newSuffixFrame(λ, [])† ∘ g8MetricVisibleBoundaryCoframe(λ, family) = 0.
```

The proof keeps the inverse-Gram square-root precomposition explicit and
applies the aggregate Schur orthogonality to that source vector; the real
upper Euler scalar is then harmless. This is a genuine same-owner statement
about the concrete metric coframe and is available to later Gram-channel
consumers. It remains only an orthogonality fact, not a radial crossing
identification or a sign theorem.

Build evidence: owning build `1465_g8_p1_visible_boundary_orthogonality.log`
completed successfully (3926 jobs), with complete audit re-readback in
`1476_g8_p1_boundary_orthogonality_audit.log`; zero `error:` and zero
`sorryAx`, and all three declarations print the standard
`[propext, Classical.choice, Quot.sound]` axioms.

Metric-to-radial transport, finite metric trace equality, P2 remainder/sign,
and the P3 producer remain open.
