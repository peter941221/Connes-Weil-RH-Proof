# 1744 - Pointwise bilateral-profile sign no-go

Date: 2026-09-20.

Status: FORMAL route screen under the healthy-`CompactLog` B5 mainline.
This is not an RH result.

`P2BilateralProfileSignWitness` requires a nonpositive archimedean term and
nonpositive bilateral profile at every visible prime power.  Its existing
consumer proves `0 <= qw`.  The new theorem
`not_pointwiseProfileSignWitness_of_healthyDetectorData` combines that fact
with the already formalized healthy-detector implication `qw < 0`, proving
that no healthy detector can carry this witness.

Therefore the B5 producer cannot be a pointwise sign argument.  It must use
positive and negative profile contributions in an aggregate compensation
inequality on the same selected owner.  This is a genuine route screen, not
a stored sign conclusion.

Verification: owning module and audit build through
`build-logs/shortest_route_20260920_pointwise_no_go.log`, with zero errors and
zero `sorryAx`; the new declaration has only the standard axiom trio.
