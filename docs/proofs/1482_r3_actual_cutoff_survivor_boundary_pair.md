# 1482 — R3 actual-cutoff survivor/boundary channel pair

**Status:** FORMAL finite-cutoff adjoint pairing for the two mixed
survivor/boundary channels in the G8 metric ledger. Their trace sum is twice
the real part of either orientation at every cutoff. No cutoff limit is
proved.

**Consumer:** the mixed-channel part of the actual G8 four-channel metric
ledger on the same healthy `CompactLog` owner. The active B5 consumer remains
`0 <= C1SameOwnerWeil.qw g` for the tower-selected detector.

The leaf
[`C1G8R3ActualCutoffSurvivorBoundaryPair.lean`](../../ConnesWeilRH/Dev/C1G8R3ActualCutoffSurvivorBoundaryPair.lean)
proves that `g8MetricCutoffChannel survivor visibleBoundary` is the adjoint of
`g8MetricCutoffChannel visibleBoundary survivor`. The identity retains the
same owner, finite prime-power family, source basis, and literal cutoff; it
uses only self-adjointness of the selected detector operator.

The second theorem combines this identity with the ordinary-trace adjoint
readback and the existing trace-class witnesses. At each finite cutoff, the
two mixed traces sum to `2 * Re(trace(boundary/survivor))`. This reduces the
two ordered mixed channels to one real sequence, but does not prove that the
sequence converges or identify its limit with the finite-prime scalar. The
survivor-survivor and boundary-boundary cutoff limits, the mixed-pair limit,
the signed remainder readback, `G8SameOwnerReadbackData`, detector
semi-local positivity, C3, and RH remain open.

The paired audit prints only `[propext, Classical.choice, Quot.sound]` for
both declarations. Acceptance log `0915_survivor_boundary_pair_try2.log`:
`Build completed successfully (3958 jobs)`, zero `error:` lines, zero
`sorryAx`, and two `Quot.sound]` occurrences.
