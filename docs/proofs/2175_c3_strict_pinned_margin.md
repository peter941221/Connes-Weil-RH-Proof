# 2175 — Strict pinned C3′ determinant margin

Date: 2026-09-29.

Status: **FORMAL OWNER-SOCKET PROGRESS**. The result strengthens the pinned
two-span C3′ phase budget. It is not the final selected-detector sign
certificate and it does not imply RH.

## Consumer and owner

The consumer is the same C3′ two-span owner socket used by
`CarrierTwoSpanDeterminantCertificate.gate`: one carrier frequency, the
finite visible-prime owner attached to that carrier, and the exact aggregate
phase budget. The healthy input is the actual `CompactLogTest` carried by
`HealthyYoshidaDetectorData rho g`; the second span is the existing
`narrowArchRoot`, demodulated and re-modulated on that same carrier.

## New theorem

`strict_carrier_twoSpan_determinant_margin_of_pinned_geometry` proves that,
for every carrier frequency `γ`, there is an explicit positive margin

```text
μ = (-ICgate narrowArchRoot.convolutionSquare)
      * ICgate g.convolutionSquare > 0
```

such that the exact two-span determinant satisfies

```text
ICgate(u.square) * ICgate(v.square)
  - ICgate(u.involution.convolution v)^2 ≤ -μ,
```

where `u = carrierModulate γ (carrierModulate (-γ) narrowArchRoot)` and
`v = carrierModulate γ (carrierModulate (-γ) g)`. The proof uses the strict
negative narrow-root gate, the strict positive healthy pivot, and only the
nonnegativity of the retained cross-channel square. No cross-channel sign is
assumed or split into separate channel claims.

`strict_carrier_twoSpan_phase_budget_of_pinned_geometry` then reads the same
margin through the exact determinant/phase identity, yielding

```text
carrierArchimedeanDeterminantPhase γ u₀ v₀
 + carrierMixedDeterminantPhase γ u₀ v₀
 + carrierPrimeDeterminantPhase γ u₀ v₀ ≤ -μ,
```

for `u₀ = carrierModulate (-γ) narrowArchRoot` and
`v₀ = carrierModulate (-γ) g`.

This is a quantitative strengthening of the existing nonpositive phase
budget on the same owner. Support containment and the final selected-span
triple-vanishing/detection hypotheses remain separate caller obligations.

## Evidence

- implementation: `ConnesWeilRH/Dev/C1C3StrictPinnedMargin.lean`;
- paired audit: `ConnesWeilRH/Dev/C1C3StrictPinnedMarginAudit.lean`;
- module build: `results/20260929_c3_strict_margin_build4.log`;
- audit build: `results/20260929_c3_strict_margin_audit_build5.log`;
- both builds ended with `Build completed successfully` and zero `error:` lines;
- audited declarations depend only on `[propext, Classical.choice, Quot.sound]`;
  no `sorryAx` occurs.

## Boundary

The margin is attached to the pinned root/healthy-owner pair. It does not yet
prove that the final selected detector has the required support, vanishing,
detection, and full spectral-tail compatibility. The remaining producer task
is therefore to transport this strict owner margin to the selected span under
those named hypotheses, or prove a separate same-owner physical-kernel bound.
