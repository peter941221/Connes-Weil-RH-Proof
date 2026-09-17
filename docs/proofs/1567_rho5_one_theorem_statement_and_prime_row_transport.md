# 1567 — ρ5 one-theorem statement and canonical-family prime-row transport

Date: 2026-09-17.

**Status: FORMAL statement pinning plus definition transport.** No tail
estimate, no positivity, no sign premise, and no RH conclusion is present or
claimed. Consumer: the ρ5 gate of the healthy-`CompactLog` B5 same-owner G8
readback (records 1502/1504). This brick executes the pre-registered item 6
of record 1503 section 6: the ρ5 identification is stated ONCE, with both
sides pinned and the Euler content exposed term by term.

## Landed declarations

`ConnesWeilRH/Dev/C1G8R5EulerContentBridgeTarget.lean` with its paired
`...Audit` leaf:

| declaration | content |
| --- | --- |
| `g8R5EulerContentBridge` | the ρ5 gate as one named `Prop`: `re (ordinaryTraceAlong sourceBasis (J† C† G C J)) = qw owner.sourceTest`, with `G = (I + N†)† W (I + N)` from the committed adjoint-shear Gram |
| `g8R5EulerContentBridge_iff_psiComponents` | right side pinned to the committed split `poleTerm - archimedeanTerm - finitePrimeSum` of `psi` on the half-density square (`qw_eq_psi_square`, `psi_eq_components`); signs transcribed from the committed names, not from prose (law F22) |
| `g8R5EulerContentBridge_iff_fourChannels` | left side pinned to the base channel, the two adjoint shear cross channels, and the leakage square, via the committed operator identity `g8EndpointSourceCutoffLimitOperator_eq_fourTerms` — the same channels whose limits `rho2`/`rho3`/`rho4` already supply (record 1511) |
| `g8R5CanonicalArithmeticRow_eq_finitePrimeSum` | same detector, same prime set: at the canonical exact-support family the arithmetic sum `∑ pm ∈ (g8CanonicalFamily owner).terms, owner.finitePrimeTerm (p^m)` re-reads exactly `finitePrimeSum owner.sourceTest.convolutionSquare` |
| `ordinaryTraceAlong_g8CanonicalArithmeticOperator_eq_finitePrimeSum` | the full arithmetic row of the 1563 ledger: under the same support and trace-basis premises as record 1564's supplier, `re (ordinaryTraceAlong globalBasis (arithmeticOperator owner (g8CanonicalFamily owner))) = finitePrimeSum owner.sourceTest.convolutionSquare` |

The transport proof is pure definition movement: the family terms identify
with the canonical prime-power terms (record 1464 machinery), those telescope
through `canonicalPrimePowerTerms_sum_eq_selectedFinitePrimeTerm_sum` to the
computed index set of the owner, the two computed index sets coincide by
`globalExact` membership extensionality (the differing `supportRadius`
fields drop out), and the summands agree pointwise because
`SelectedWeilSquareOwner.convolutionSquare` and `primePowerValue` read only
`sourceTest`; `finitePrimeSum_square_eq_selected` closes the right side.
No estimate, convergence, or trace-cycle input is used.

## Ledger consequence for the ρ5 attack (paper accounting, zero new premises)

The pinned statement exposes where the prime content can and cannot live. The
committed prefix ledger (record 1563 section) reads

```text
tr_prefix(A_G8)
  = tr_prefix(arithmeticOperator)      \  + sum of prime terms (row supplied above)
  + tr_prefix(sameObjectResidual)      /  - same sum by its very definition:
                                          sameObjectResidual := projectionResponse
                                                                - arithmeticOperator
  + tr_prefix(rootCycleDefect)
  + tr_prefix(Delta_G8)
```

so the aggregate contains the visible prime-power sum TWICE with opposite
signs, and the only surviving carrier of prime content inside
`tr_prefix(A_G8)` is the difference of those two rows (equivalently the
`projectionResponse` row) plus the cycle and correction rows. Therefore:

- the naive allocation "prime row -> `finitePrimeSum`, residual row ->
  archimedean, cycle -> 0, correction -> 0" is NOT consistent with the target
  `pole - arch - prime` under the committed definitions;
- any valid ρ5 producer must control the COMBINED rows against the pinned
  three-component right side, exactly as this leaf now states it;
- row-by-row vanishing assumptions are precluded, which was the standing
  audit question from the wave-strategy review.

This is an accounting consequence of committed definitions, not a no-go: the
bridge remains open and this record claims no disproof of any route.

## P2 sub-limit split status

The leakage-channel engine `sourceBandGramResponse_eq_soninFirstJet_sub_remainder`
(`CCM24FiniteSActualBandSourceRemainder.lean:628`) is committed at the Source
level: the prime-window residual (P2 sub-limit) subtracted from the Sonin
first jet. The remaining formal connector is the transport from that identity
to the leakage-square limit object `L` inside the pinned bridge; it is the
named follow-up brick, not part of this record.

## Boundary and acceptance

The ρ5 gate itself, the (★) square-sum, the residual/cycle/correction
estimates, and the source/ambient trace transport all remain OPEN; WO-S and
WO-B in map 042 are unchanged. RH is not claimed.

Acceptance: try1 `1743_r5_bridge_target_try1.log` failed on missing
`CCM24FiniteSGramResponse`-family opens for the carrier abbreviations; try2
`1744_r5_bridge_target_try2.log` leaked two goals; try3
`1745_r5_bridge_target_try3.log` is GREEN: footer
"Build completed successfully (3972 jobs)", zero `error:` lines, zero
`sorryAx`, and all five declarations print exactly
`[propext, Classical.choice, Quot.sound]`.
