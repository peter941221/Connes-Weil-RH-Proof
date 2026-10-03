Record 2544: third-derivative endpoints for production cell 5440

The target is the unchanged 30-family owner at sigma = +1/2, on the
exact grid cell with endpoint indices 5440 and 5441. Each endpoint is
inside all 30 supports. Stored widths are squared; signed modulation and
the coefficient boxes from record 2338 are unchanged.

Sixty endpoint certificates bound actual third derivatives. Each uses
the exact derivative multiplier from 2543 and the compact exponential
evaluator from 2542. Scalar norm bounds include the multiplier-amplified
exponential error. The norm of each complex approximate product is bounded
by exact comparison of its squared real and imaginary coordinates.

The independent reader derives the third multiplier as a^3 + 3ab + c,
where a, b and c are the first three derivatives of the exponent. This
does not reuse the generator's bump-polynomial ladder. It checks every
exponential trace and rejects a corrupted multiplier and a zeroed norm
upper. Default midpoint generation remains identical to record 2543.

The assembly module replaces the two endpoint norms in the existing 2538
third-derivative cell bound. It retains the original fourth-derivative
envelope as an unevaluated expression. The signed midpoint bound from
2543 then yields a curvature bound with that remaining expression.

This is not a numerical whole-cell integral certificate. Fourth-envelope
evaluation and the right endpoint's signed order-zero aggregate remain
open, followed by the remaining grid, exact coefficient membership and
the complete selected-owner signed budget.

The first assembly build failed because add_le_add_right was applied to
the wrong addition position. Explicitly unfolding the cell terms and
using add_le_add with reflexivity on the unchanged fourth term fixes the
proof interface without altering any bound. Failed-build axiom output
is not acceptance evidence; the final successful build and independent
readback must both pass.

Evidence

Final acceptance passed: 4545 build jobs, 127 audited declarations with
exactly propext, Classical.choice and Quot.sound, and 734 byte-identical
project dependency sources plus build configuration. The independent
reader passed both endpoints and all 60 families, with no new-module
warnings. This acceptance includes the assembly module and root build.

ConnesWeilRH/Dev/C1RouteAEndpointLeftThird2544.lean
ConnesWeilRH/Dev/C1RouteAEndpointRightThird2544.lean
ConnesWeilRH/Dev/C1RouteAEndpointLeftNorms2544.lean
ConnesWeilRH/Dev/C1RouteAEndpointRightNorms2544.lean
ConnesWeilRH/Dev/C1RouteAThirdCellEndpointAssembly2544.lean
scripts/validate_endpoint_thirds_2544.py
results/2544_endpoint_readback.json
