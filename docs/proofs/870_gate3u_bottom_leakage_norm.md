# Gate-3U unit-scale bottom: the leakage-norm `<= 1` (Proof-717) identity

Date: 2026-08-07. Status: **located, not closed**.

## The exact Gate-3U premise at unit scale

`canonicalRealGate3UAt_unit_of_rightEnergy` (`CCM24UnitScaleCanonicalGateHandoff.lean`)
reduces Gate 3U at `lambda = unitSoninScale` to ONE open premise

```
hright :
  sourcePhysicalCoframeCompletedKernelRightEnergy ≤ fixedPhysicalEnergyMajorant
```

Every prior `hfactor`/HS premise is already discharged by the axiom-clean
`sourceProlateHilbertSchmidtFactor_unit_summable` (unit-scale closure).

## What is already bounded

- `fixedPhysicalEnergyMajorant` = `6*(c-a)^2*seminorm^2 + (1+|detector|^2)*sum|Prolate|^2`
- LEFT inclusion leg: `sourceThreeBoundaryPairData_left_basisEnergy_le_fixedMajorant`.
- RIGHT basis energy on the GLOBAL basis:
  `sourceThreeBoundaryPairData_right_basisEnergy_le_fixedMajorant`.

## The crux: `hright` is `right ∘ leakage` on the SOURCE basis

`hright := sum_i |right (sourcePhysicalCoframeLeakage lambda family (sourceBasis i))|^2`.
Precomposing `right` by the bounded leakage via the library lemma
`boundedPrecomp_right_tsum_le_of_norm_le_one`
(`CCM24FiniteSFixedQuotientContractionBound.lean:96`) reduces it to needing

```
|sourcePhysicalCoframeLeakage| <= 1
```

The endpoint-guard library already pins that this is the Proof-717 cancellation identity
(`sourceActualBandCombinedCoframeLeakage_eq_zero_of_norm_endpoint_le_one`),
i.e. `forward + physicalLeakage = 0`.

## Numeric verdict (docs/proofs 815-824)

The outer transport-leak does NOT decay (plateau ~ 0.62), so `|leakage| <= 1` is
generically FALSE on the real carrier. Only the degenerate `visiblePrimes = []`
carrier (leakage = 0) closes it. The re-type sign/trace work (`CompactLogDetectorTraceBridge`+A3+852)
closes `0 <= positiveTrace` axiom-clean on the Hilbert carrier but is a DIFFERENT lane and does NOT
close this energy wall.

## Conclusion

Gate 3U at unit scale is exactly the Proof-717 physical
`forward + physicalLeakage = 0` cancellation (equivalently `|leakage| <= 1`), a real open analytic
identity. Progress requires that cancellation (or a fresh energy bound on `right∘leakage`), not more
trace/signification machinery. Not yet closed.

## Addendum (same day): the norm>=1 obstruction makes |leakage| <= 1 degenerate

CCM24FiniteSEndpointContractionGuard proves unconditionally (axiom-clean, on any `[Nontrivial]`
carrier) that `1 <= |sourceActualBandForwardEndpointCoframe|`
(`one_le_norm_sourceActualBandForwardEndpointCoframe`), with
`coframe = sourceInclusion + combinedLeakage` and
`|coframe| <= 1 <-> combinedLeakage = 0`
(`sourceActualBandCombinedCoframeLeakage_eq_zero_of_norm_endpoint_le_one`/
`..._eq_inclusion_add_leakage`). So the `hright` premise (via `boundedPrecomp_right_tsum_le_of_norm_le_one`
reduces to `|leakage| <= 1`) holds only in the degenerate collapse `leakage = 0`. Numerics
(docs 815-824) put the forward coframe norm strictly above 1, so leakage is genuinely nonzero.
Gate-3U unit bottom = open Proof-717 identity `forward + physicalLeakage = 0`
(equivalently `|leakage| <= 1`); without it (or a fresh quantitative `right∘leakage` energy bound)
the gate cannot be closed by Lean rearrangement above.
