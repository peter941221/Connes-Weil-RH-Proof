Record 2547: derivative precision at support-boundary cells

Fixed 100-bit coordinates fail the named local derivative-error allowance
on the boundary-cell test set. The test covers 48 cells: the two neighbors
of each support-crossing cell, the crossing cell itself, and control cells
0, 5120, 5440 and 10239, deduplicated. Both sigma signs give 96 cases.
The allowance is 1e-8 per cell for the specified derivative-evaluation
contributions. This is not a global impossibility statement or a full
integral budget verdict.

At 100 bits, 56 cases exceed the allowance. The worst is cell2700,
sigma+1/2, at 1.6499825279800327e-6. At 160 bits all 96 pass; the largest
charge is 9.76822961007476e-21 at cell5440, sigma+1/2. The 100-bit path
matches the accepted evaluator's center, radius and squaring depth exactly
in 2968 comparisons. The input coefficients, widths and modulation are
unchanged.

The second-derivative contribution is evaluated at the actual cell
midpoint and multiplied by h^3/12. The third-derivative contribution uses
both actual endpoints, sums the per-family maximum error and multiplies
by h^4/24. The precision pricing carries center/radius rounding for the
second derivative and the scalar norm-bound rounding allowance for the
third derivative. The fourth-envelope contribution, coefficient-range
uncertainty and full integral remain outside this probe's scope.

Exact aggregate rational denominators exceeded Python's default integer
text-conversion limit in the first run. The completed run exports charges
rounded upward to 2^-160 and checks that the allowance decision agrees
with the unrounded exact rational. Positive charges are never exported
as zero. The failed initial export is not acceptance evidence.

The 160-bit Lean evaluator retains 19 Horner steps and the original
1e-18 Taylor allowance. Coordinates round down at 160 bits, the scalar
coordinate error is 2^-159, and propagated radii round up at 200 bits.
The proof reuses the accepted analytic Horner/square lemmas. The original
100-bit evaluator is unchanged.

Concrete owner replay

Within the worst cell2700, the largest coefficient-weighted endpoint
third-derivative evaluation error at 100 bits comes from family15 at
node2701. This is an interior support point and requires 16 squarings.
The new boundaryThirdError2547 theorem certifies its actual derivative
using the 160-bit evaluator and the exact derivative multiplier. The
independent reader replays the rational arithmetic and derives that
multiplier as a^3 + 3ab + c from exponent derivatives. A zeroed error
radius is rejected. This is one endpoint derivative, not a completed
boundary-cell integral.

Final acceptance passed: 4539 build jobs, six declarations with exactly
propext, Classical.choice and Quot.sound, 728 matching dependency sources
and matching build configuration, with no new-module warnings. The concrete
unit third-derivative error bound is approximately 3.1213818490809767e-26.

Next steps

1. Use the accepted higher precision in actual boundary-cell endpoint and
   midpoint certificates; completion requires both support-interior and
   exact exterior-zero branches for every family.
2. Evaluate the matching fourth envelopes and assemble complete boundary
   cells, then measure batch verification cost before grid replication.
3. Retain exact coefficient membership and the complete selected-owner
   signed budget as distinct obligations beyond these cell certificates.

Evidence

results/2547_boundary_precision.json
results/2547_boundary_readback.json
ConnesWeilRH/Dev/C1RouteACompactExp1602547.lean
ConnesWeilRH/Dev/C1RouteABoundaryReplay2547.lean
scripts/price_boundary_precision_2547.py
scripts/generate_compact_exp160_2547.py
scripts/generate_boundary_replay_2547.py
scripts/validate_boundary_replay_2547.py
