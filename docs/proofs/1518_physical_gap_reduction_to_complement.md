# Physical gap reduction to the source-Sonin complement

Date: 2026-09-17

The theorem `compositeGapLeg_sourceColumn_normSq_summable_of_complement`
proves the exact analytic reduction needed by the B4 boundary consumer.  For
every factored physical column `M ∘L J ∘L N`, assume square-summability only
for the gap operator applied to `(id - P) ∘L M ∘L J`.  The theorem combines
that hypothesis with the unconditional source-range estimate from record
1516 and the pointwise split from record 1517, using the standard
Hilbert--Schmidt sum bound, to obtain square-summability of the complete gap
leg.

Therefore the B4 gap obligation has one named remaining target: the
complement input `(id - P) ∘L M ∘L J` for the actual boundary factors.  No
estimate for this complement is supplied here, and WO-B, S3, and RH remain
open.

Validation: owning build log
`/home/peter/rh/build-logs/1656_gap_complement_reduction.log`; paired audit log
`/home/peter/rh/build-logs/1657_gap_complement_reduction_audit.log`.  Both
completed with zero `error:` and zero `sorryAx`; the audit has only the
standard three axioms.
