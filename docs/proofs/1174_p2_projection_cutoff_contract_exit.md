# Record 1174 — P2 projection-cutoff contract exit

Date: 2026-09-06

## Result

`P2BilateralProfileAggregateWitness.of_projectionCutoffLimitContracts`
converts the existing windowed projection owner
`cutoffProjectionOperator = C_n† K C_n` into the exact P2 aggregate socket.
The theorem
`sourceRH_of_healthyDetector_p2ProjectionCutoffLimitContracts` consumes such
contracts for every right-oriented off-line zero and reaches the healthy B5
`SourceRH` contradiction.

The cutoff operator's positivity and trace-class fields are already formal.
The producer still must prove its remainder tends to zero and its corrected
trace reads back to the same-owner `qw`.

The focused owner/audit build completed successfully in 3777 jobs, with no
`error:` lines or `sorryAx`; the audit reports only
`[propext, Classical.choice, Quot.sound]`.

## Route meaning

This is the viable windowed/renormalized Stage-3 route after the bare
convolution no-go.  P2/RH remain open.
