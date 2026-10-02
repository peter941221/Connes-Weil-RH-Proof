# Record 2490: owner-family hybrid curvature monotonicity

The production owner-family curvature consumer now takes the pointwise minimum
of the endpoint-safe interval curvature and the same family's L1 derivative
budget on safe cells. The unsafe branch remains the L1 budget, so the change
does not weaken the derivative bound or change the owner.

Two Lean interfaces make the numerical direction explicit:

- `ownerFamilyHybridCurvature_le_familyL1Sum2488` proves the hybrid cell
  curvature is bounded by the sum of the 30 family L1 curvatures.
- `localCurvatureRemainder_familyHybrid_le_familyL1Sum2488` transports that
  pointwise inequality through the nonnegative `step^3 / 12` remainder weight.

The paired audit build completed successfully at 3737 jobs. All audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`. This is a
formal budget-shrink interface, not a numerical certificate, producer GO, or
RH proof. The same-grid 2489 price remains an external non-certificate probe.
