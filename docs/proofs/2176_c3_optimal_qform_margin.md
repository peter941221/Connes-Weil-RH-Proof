# 2176 — Explicit optimal q-form margin for the pinned C3′ owner

Date: 2026-09-29.

Status: **FORMAL OWNER-SOCKET PROGRESS**. This makes the strict pinned
two-span margin directly available in the optimal q-form interface. It does
not prove the selected-detector sign or RH.

## Consumer, owner, and assumptions

The consumer is the same C3′ two-span owner socket used by
`CarrierTwoSpanDeterminantCertificate.gate`: one carrier, the exact visible
prime owner attached to it, and the determinant/phase readback. The owner is
the pair `(narrowArchRoot, g)` after carrier demodulation, where `g` is the
actual `CompactLogTest` in `HealthyYoshidaDetectorData rho g`. The proof uses
the strict negative root gate and the strict positive healthy pivot already
present in the pinned geometry.

## New formal content

`carrierTwoSpanOptimalQform` records the exact two-coordinate q-form at the
optimal coefficient

```text
λ* = - ICgate(u.involution.convolution v) / ICgate(v.convolutionSquare).
```

The theorem
`strict_carrier_twoSpan_determinant_product_bound_of_pinned_geometry` exposes
the determinant bound as the product identity

```text
det(u,v) ≤
  -((-ICgate narrowArchRoot.convolutionSquare)
       * ICgate g.convolutionSquare).
```

The theorem
`strict_carrier_twoSpan_optimal_qform_margin_of_pinned_geometry` then gives an
explicit witness

```text
μ = -ICgate narrowArchRoot.convolutionSquare > 0
```

and proves the actual optimal q-form satisfies

```text
carrierTwoSpanOptimalQform γ u₀ v₀ ≤ -μ,
```

for `u₀ = carrierModulate (-γ) narrowArchRoot` and
`v₀ = carrierModulate (-γ) g`. The positive pivot is used only to justify the
division in the exact optimal-q identity; the cross channel remains an exact
square and no channelwise sign premise is introduced.

This is a strictly smaller and more usable quantitative obligation than an
unnamed existential margin: the value passed to a q-form consumer is now
visible in the theorem statement.

## Verification

- implementation: `ConnesWeilRH/Dev/C1C3StrictPinnedMargin.lean`;
- paired audit: `ConnesWeilRH/Dev/C1C3StrictPinnedMarginAudit.lean`;
- module build: `results/20260929_c3_qform_margin_build9.log`;
- audit build: `results/20260929_c3_qform_margin_audit_build10.log`;
- root aggregate build: `results/20260929_c3_qform_margin_root_build11.log`;
- all three logs end with `Build completed successfully` and have no `error:`
  or `sorryAx`; the audited declarations use exactly
  `[propext, Classical.choice, Quot.sound]`.

## Failure boundary

The result is pinned to the auxiliary root/healthy pair. It does not supply
the selected detector's support, triple vanishing, off-line-zero detection,
or full spectral-tail compatibility, and it does not establish the final
negative physical-kernel gate. Those remain the named C3′ producer premises.
