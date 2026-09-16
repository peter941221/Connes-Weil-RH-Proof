# 1497 - R3 internal prolate-gap source energy

Date: 2026-09-16.

Status: `FORMAL SAME-BASIS HILBERT--SCHMIDT ENERGY FOR THE INTERNAL GAP AND
FULL SOURCE-SONIN LEAKAGE`. This closes the second selected-root
source-leakage channel from record 1494 and combines both channels into a
direct full-leakage estimate. It does not estimate the distinct finite
visible-prime G8 boundary outputs or give a G8 trace/readback theorem.

Consumer: the same-owner healthy-`CompactLog` B5 statement
`0 <= C1SameOwnerWeil.qw g`, through the selected detector-root leakage
decomposition and its eventual G8 trace/readback.

## Result

For every selected square owner, selected scale, and named basis of the
corresponding `sourceSoninCarrier`, Lean proves that the selected root applied
to the source quotient band has square-summable columns:

```text
Summable i =>
  norm((sourceBandProjection lambda * rootConvolution owner
    * sourceInclusion lambda)(sourceBasis i))^2.
```

This is the internal radial-but-non-Sonin gap term in record 1494 because the
source quotient-band projection is `E - P` and absorbs the radial projection
on its right.

The proof writes `B = E - P`, `Q` for the Hardy--Titchmarsh conjugate of the
radial projection, and `K = Q B` for the all-scale prolate Hilbert--Schmidt
factor. It uses the exact source-basis decomposition

```text
B C J = K† C J + E (I - Q) C J.
```

The first term is Hilbert--Schmidt by the all-scale prolate square-sum,
adjoint basis transfer, and bounded precomposition by the selected root and
source inclusion. The second term is the radial projection of the
second-support leakage. Hardy--Titchmarsh conjugates that leakage to the
reflected selected root's radial crossing. The finite compact-output window
from record 1495 gives its Hilbert--Schmidt square-sum; bounded
Hardy--Titchmarsh and radial projections preserve it. `summable_normSq_add`
combines the two terms on the same arbitrary source basis.

Finally, the exact record-1494 leakage split combines the radial-boundary
estimate from record 1496 with this internal-gap estimate. The declaration
`selectedRoot_sourceSoninLeakage_sourceBasis_normSq_summable` proves directly
that the complete selected-root source-Sonin leakage has square-summable
columns on every named source basis.

The formal declarations are in
`ConnesWeilRH/Dev/C1G8R3InternalProlateGapEnergy.lean`:

- `hardyTitchmarsh_conjugate_root_eq_reflected_root`;
- `reflectedRoot_radialCrossing_summable`;
- `reflectedRoot_radialCrossing_conjugates_to_fourierLeakage`;
- `sourceBand_rootSourceLeg_summable`;
- `selectedRoot_sourceSoninLeakage_sourceBasis_normSq_summable`.

The paired axiom audit is
`ConnesWeilRH/Dev/C1G8R3InternalProlateGapEnergyAudit.lean`.

## Limits

Together with records 1494--1496, this proves same-basis square-summability
of both terms and of the complete selected-root source-Sonin leakage. It does
not estimate the separate finite
visible-prime G8 boundary-output energies, prove the actual G8 diagonal
limits, identify the G8 trace limit with `qw`, establish detector-specific
semi-local positivity, close C3, or prove RH. No trace-class claim is made for
the individual Hilbert--Schmidt channels.

Acceptance log: `0916_internal_gap_audit_try4.log` —
`Build completed successfully (3296 jobs)`, zero `error:` lines, zero
`sorryAx`, and five `Quot.sound]` audit terminators. All five declarations
depend exactly on `[propext, Classical.choice, Quot.sound]`.
