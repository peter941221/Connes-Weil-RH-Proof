# Record 1167 — P2 pinned explicit-range exit

Date: 2026-09-06

## Result

`sourceRH_of_pinnedOrbitDetector_p2BilateralProfileRangeWitness` consumes, for
each right-oriented off-line `rho`, a same-owner `g,n` with
`HealthyYoshidaDetectorData`, source support
`support(g.test) ⊆ Ioo (-(n+2)) (n+2)`, and
`P2BilateralProfileRangeWitness g (2*(n+2))`.

The formal proof propagates source support to convolution-square support,
invokes `P2BilateralProfileRangeWitness.toAggregate`, and then applies the
existing same-owner `qw ≥ 0` / `SourceRH` exit.  The focused owner/audit build
completed successfully in 3721 jobs, with no `error:` lines or `sorryAx`; the
audit reports exactly `[propext, Classical.choice, Quot.sound]`.

## Route meaning

All quantifier and support/cutoff glue for this P2 formulation is now formal.
This does not prove the signed range estimate (nor the equivalent positive
semi-local trace readback), so P2 and RH remain open.
