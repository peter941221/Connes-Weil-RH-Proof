# Source-range boundary gap leg

Date: 2026-09-17

The theorem `compositeGapLeg_sourceRangeColumn_normSq_summable` in
`ConnesWeilRH/Dev/C1G8R3CompositeBoundaryEnergy.lean` proves the generic B4
internal-gap square-sum for a source-range column.  Given a bounded source
column `A`, the proof factors through the source inclusion `J` and source
Sonin projection `P`, establishes `P (P A J†) J = (P A J†) J`, and invokes the
existing composite gap reducer.  The new support theorem from record 1515
therefore supplies the Hardy premise automatically; no separate Hardy
support assumption is carried by this branch.

This closes the `P`-projected component of the B4 boundary energy obligation.
For either physical boundary column, the missing statement is still the
source-range decomposition and control of the complementary `(I - P)` input.
Consequently WO-B and the S3 survivor estimate remain open.  This theorem is
a formal interface result, not a positivity theorem and not an RH proof.

Validation: owning module build log
`/home/peter/rh/build-logs/1651_source_range_gap_leg.log`; paired audit build
log `/home/peter/rh/build-logs/1652_source_range_gap_leg_audit.log`.
Both builds completed successfully with zero `error:` and zero `sorryAx`; the
audit prints only the standard three axioms.
