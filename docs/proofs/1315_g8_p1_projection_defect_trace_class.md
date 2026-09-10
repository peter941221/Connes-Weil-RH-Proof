# G8 P1 projected--complement trace-class owner

Date: 2026-09-11.

The import-facing leaf `C1G8P1MetricProjectionDefectTraceClass` constructs an
explicit Hilbert--Schmidt pair for the projected--complement channel. Its
trace product is exactly
`g8MetricCutoffProjectedLeg† · g8AdjointShearGram ·
g8SourceCutoffComplementLeg`, and the channel is proved trace-class along the
same source basis. The leaf also packages trace-class legality for all three
projection-defect channels, using the existing owners for the two complement
channels. This supplies legal trace handling without cycling an unproved
infinite product.

No sign, vanishing, metric-to-radial transport, endpoint production, P2
remainder/sign, or P3 conclusion is asserted.

Evidence: `1498_g8_p1_projection_defect_trace_class.log`, owning and audit
targets green (3927 jobs), zero `error:`/`sorryAx`; both audited declarations
use exactly `[propext, Classical.choice, Quot.sound]`.

Cross-import evidence: `1499_g8_p1_p2_p3_projection_trace_cross.log` rebuilt
this pair owner with the projection ledger/factorization, diagonal P1,
canonical P2, and same-detector P3 leaves (3983 jobs), again with zero
`error:`/`sorryAx`.

The aggregate three-channel audit was reverified in
`1503_g8_p1_projection_defect_all_trace_class.log` (3927 jobs), with the same
axiom set and no errors.

The final P1/P2/P3 consumer batch `1504_g8_p1_p2_p3_full_consumer_batch.log`
also rebuilt this owner with the defect ledger, metric factorization, diagonal
P1, canonical P2, and same-detector P3 leaves (3983 jobs), with zero
`error:`/`sorryAx`.

RH is not claimed.
