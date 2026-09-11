# 1324 — G8 P1 radial crossing energy transport

Date: 2026-09-11.

Status: FORMAL Lean brick. It transports a named column-energy premise into
an explicitly owned trace-class positive defect on the radial side. It proves
no summability of the column energy itself, no vanishing, no cutoff limit, no
metric-to-radial transport, and no RH statement.

## Statement

Let `C = radialSoninBoundaryCrossing p S` on `finiteSCarrier`, and let
`sourceBasis` be any Hilbert basis. If the pulled-back antiresonant-column
basis energy is summable,

```text
sum_i || newFrameAntiresonantColumn p S (frame†(e_i)) ||^2 < infinity,
```

then Lean proves:

1. `sum_i || C e_i ||^2 < infinity`, with the visible canonical termwise cost
   `(32 ||q_p^{-1}||)^2` per basis index;
2. the positive Cauchy defect `C†C` is `IsTraceClassAlong sourceBasis`;
3. the explicit pair `radialCauchyPairDataOfAntiresonantColumnEnergy` has
   `traceProduct = C†C` exactly (owned, not merely dominated).

This closes the conditional chain left open by the full-carrier extension
(Proof 687 chain): the radial side now needs exactly one named analytic
input — the summability of the antiresonant-column pullback energy — of the
same kind as the single raw cutoff-leg energy `E_A(n)` left open on the
metric side (records 1321–1323).

## Lean owner

`C1G8P1RadialCrossingEnergyTransport.lean`, paired audit declarations:

```text
normSq_radialSoninBoundaryCrossing_apply_le_canonical_antiresonantColumn
summable_radialSoninBoundaryCrossing_normSq_of_antiresonantColumnEnergy
isTraceClassAlong_radialSoninBoundaryCauchyDefect_of_antiresonantColumnEnergy
radialCauchyPairDataOfAntiresonantColumnEnergy_traceProduct_eq_defect
```

## Verification

Batch `1538_g8_p1_radial_transport_batch_retry11.log`: 4074 jobs, zero
`error:` and `sorryAx`; every audit declaration prints only
`[propext, Classical.choice, Quot.sound]`.

RH is not claimed.
