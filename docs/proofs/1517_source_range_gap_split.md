# Source-range split of the physical boundary gap leg

Date: 2026-09-17

The theorem `g8AmbientSourceLeg_gapLeg_pointwise_eq_sourceRange_add_complement`
in `ConnesWeilRH/Dev/C1G8R3BoundaryOutputFactorizationBridge.lean` gives the
exact pointwise decomposition of the internal-gap output for a factored
boundary column `M ∘L J ∘L N`.  Writing `P` for the source-Sonin projection,
the gap output is the sum of the same gap operator applied to `P ∘L M ∘L J`
and to `(id - P) ∘L M ∘L J`.

Combined with record 1516, the first summand is square-summable unconditionally.
The physical B4 obligation is therefore reduced to the complementary input
`(id - P) ∘L M ∘L J`; no cancellation or positivity of that complement is
asserted.  This is a formal algebraic reduction and does not close WO-B, S3,
or RH.

Validation: owning build log
`/home/peter/rh/build-logs/1653_gap_split.log`; paired audit log
`/home/peter/rh/build-logs/1654_gap_split_audit.log`.  Both completed with zero
`error:` and zero `sorryAx`; the audit has only the standard three axioms.
