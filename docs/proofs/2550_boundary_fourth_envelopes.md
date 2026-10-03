Record2550: fourth envelopes across the cell2700 support boundary

The numerical fourth envelopes retain the existing2538formula at sigma+1/2
for the unchanged30-family owner. Twenty-eight families have a nonempty
support intersection with the cell. Families0and5 are entirely exterior;
their cell allowance is zero, matching the exterior branch of the original
third-derivative cell bound.

Both endpoints are negative. The normalized near distance is the smaller
endpoint absolute value divided by the squared stored width; the far
distance is the larger endpoint absolute value, clamped at the support
radius before division. For22families the far ratio is exactly1. Clamping
is used in the original interior-support envelope; it is not asserted as
a bound on all exterior points.

The exact exponent is max(sigma*a,sigma*b)-30/(1-near^2). Its evaluation
uses160-bit coordinates and200-bit propagated radii. The frequency square
root is rounded upward, and the complete fourth upper rounds upward on
the160-bit grid. The same factorization theorem from2545 is reused without
inverse-deficit capping or changes to signed modulation. Default generation
of the prior2545payload remains byte-identical.

The independent reader reconstructs the exact geometry and exponent,
derives bump polynomials through their derivative recurrence, replays
the160-bit exponential arithmetic and checks the final rational inequality.
It rejects a zeroed upper on a support-crossing family. Exterior entries
must have zero upper and no exponential payload.

The assembly module connects these numeric fourth bounds to the accepted
endpoint third norms, retaining the original support split. It then sums
coefficient-weighted allowances and combines them with the signed midpoint
upper from2549. The resulting aggregate is still an explicit finite sum;
its final numerical total and the endpoint order-zero signed bounds are
the next inputs for the cell-integral consumer.

This does not yet certify the complete boundary-cell integral, full grid,
exact coefficient membership or selected-owner positivity.

Final acceptance passed:4554build jobs,34audited declarations with exactly
propext, Classical.choice and Quot.sound,743matching dependency sources and
build configuration, no new-module warnings. Independent rational replay,
regeneration, exact exterior classification and corruption rejection passed.

Evidence

ConnesWeilRH/Dev/C1RouteABoundaryFourth2550.lean
ConnesWeilRH/Dev/C1RouteABoundaryAssembly2550.lean
scripts/generate_boundary_fourth_2550.py
scripts/validate_boundary_fourth_2550.py
results/2550_boundary_fourth_readback.json
