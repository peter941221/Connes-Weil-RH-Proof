# Record 1804 — C3' Round 1 owner closure

Date: 2026-09-22.

Status: Round 1 complete at the formal owner boundary. The C3' signed
inequality and RH are not proved.

## Consumer served

This record serves the binding healthy-`CompactLog`, B5-shaped route selected
by map record 1076. It does not open a universal B1 campaign, a density lift,
or the normalized additive B5 owner.

## What is now one owner

`ConnesWeilRH/Dev/C1C3CarrierTransport.lean` packages the carrier frequency,
the two compact-log envelopes, their support hypotheses, the positive BB
pivot, and the exact phase budget in
`CarrierTwoSpanDeterminantCertificate`. Its `gate` theorem feeds the existing
`orbitWindowSemiLocalGate` consumer.

The budget is exactly the sum of three same-owner consumers:

```text
Archimedean determinant
+ mixed Archimedean/prime discrepancy
+ prime determinant
<= 0
```

The preceding formal bricks provide the carrier transport, finite visible
prime phase-cell readbacks, positive/negative credit-deficit decompositions,
the determinant split, and the optimal two-span coefficient reduction. The
paired `C1C3CarrierTransportAudit` prints their axioms.

## Boundary kept open

The owner closure supplies no sign. In particular, `c3Sigma` negativity is
an Archimedean profile result on its own owner; it is not silently identified
with the full detector-specific determinant budget. Round 2 must prove the
actual signed estimate, including the mixed and prime consumers, or produce a
named counterexample to this C3' producer shape.

## Evidence

- Formal owner: `ConnesWeilRH/Dev/C1C3CarrierTransport.lean`.
- Paired audit: `ConnesWeilRH/Dev/C1C3CarrierTransportAudit.lean`.
- Route owner record: `docs/map/080_c3p_signed_certificate_owner.md`.
- Binding route: `docs/map/003_b1_b5_minimal_exit_route_selection.md`.

This is formal project evidence. The mathematical inspiration and the
carrier/sigma strategy remain separately attributable to cited prior art and
project records; no originality or RH claim is made here.
