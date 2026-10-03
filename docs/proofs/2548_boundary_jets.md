Record 2548: complete endpoint/midpoint derivative payloads for cell2700

All 30 families now have certified third-derivative errors at each endpoint
and second-derivative errors at the midpoint, sigma = +1/2. The owner,
squared stored widths, signed modulation and exact grid are unchanged.
Interior points use the 160-bit compact evaluator from record2547.
Exterior points use the exact all-order support-zero theorem, not numerical
underflow or a rounded zero approximation.

Support geometry differs substantially across this cell. The left endpoint
has six active families (1,2,3,4,6,7) and 24 exterior families. The midpoint
and right endpoint each have 28 active families; only families0 and5 are
exterior. This is why the original all-interior cell5440 template could
not simply be copied.

The independent reader checks each support inequality against the exact
stored squared width, derives the interior multiplier by exponent
differentiation, replays every 160-bit rational exponential trace and
rejects a zeroed interior multiplier. Exterior payloads must have zero
center, factor and error and an all-order zero theorem. Regeneration is
checked separately. The older single-family2547 generator and reader were
extended without changing their default output; the prior2547 acceptance
artifact was reproduced byte for byte.

The initial exterior proofs required an explicit complex-coordinate zero
identity: embedPair2542 (0,0) = 0. After this representation fix, all three
modules and the root build passed. Final acceptance:4541jobs,93 audited
declarations with exactly propext, Classical.choice and Quot.sound,
730 byte-identical dependency sources/configuration and no new warnings.

Fourth-envelope decision

The exact-rational pricing probe tests the existing fourth envelope at
160-bit precision. Its coefficient-weighted integral contribution is
bounded by approximately5.798406853868124e-17, below the trial1e-8 local
allowance. A proposed cap at inverse deficit4 changes this only to
5.79537134170007e-17. Since the direct form already passes, no capped
transfer theorem is needed for this cell and none is claimed.

The probe's exponential argument is realized through a synthetic scalar
input solely to reuse the tested evaluator arithmetic. Owner geometry
and signed modulation remain in the original envelope coefficients.
This price is not a Lean fourth-envelope or whole-cell certificate.

Next steps

1. Produce the numeric third norms and signed midpoint aggregate from the
   accepted jets, retaining positive error radii on rounded-zero centers.
2. Certify the original fourth envelopes with near/far ratios clamped only
   as allowed by the support-crossing theorem, then assemble the cell bound.
3. Extend actual cell coverage and measure batch cost; exact coefficient
   membership, correction channels and full selected-owner positivity remain
   separate obligations.

Evidence

results/2548_boundary_jets_readback.json
results/2548_boundary_fourth_price.json
ConnesWeilRH/Dev/C1RouteABoundaryLeft2548.lean
ConnesWeilRH/Dev/C1RouteABoundaryRight2548.lean
ConnesWeilRH/Dev/C1RouteABoundaryMidpoint2548.lean
scripts/generate_boundary_jets_2548.py
scripts/validate_boundary_jets_2548.py
scripts/price_boundary_fourth_2548.py
