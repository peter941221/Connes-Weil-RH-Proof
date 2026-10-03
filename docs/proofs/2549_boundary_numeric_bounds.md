Record 2549: numeric endpoint and signed midpoint bounds for cell2700

The accepted cell2700 jets now supply all60 scalar third-derivative endpoint
norm bounds and a signed midpoint second-derivative upper
8777/50000000 = 0.00017554 at sigma+1/2. This is the unchanged30-family
owner with squared stored widths and signed modulation. It is not yet a
whole-cell integral certificate.

Endpoint norms use the160-bit base exponential centers and their proved
errors. Exact multiplier-times-center products are bounded by comparing
their squared real and imaginary coordinates to an upward rational square
root; the final scalar upper rounds upward on a2^-160 grid. The inherited
multiplier-amplified exponential error remains charged. Exterior functions
are already exactly zero by2548; this uniform scalar-bound exporter retains
a harmless positive rounding allowance even for such zero functions.

The midpoint assembly preserves the signed sum before taking its norm.
Products are rounded to the existing100-bit center grid, with2^-99 scalar
rounding allowance and upward2^-140 error radii. The underlying exponential
evaluation remains160-bit. The combined coefficient-weighted evaluation
and new rounding charge is approximately1.3607532700698279e-15, below the
formal1e-8 allowance. The final1e-7 margin also covers the coefficient-box
uncertainty. This explicitly distinguishes evaluator precision from the
subsequent signed-sum storage precision.

Validation

The old2544 norm and2543 signed-midpoint templates accept optional source
payloads while preserving their original defaults byte for byte. The
boundary wrapper changes only identified declaration prefixes and source
imports; generic analytic references retain their original names.

Independent exact readback checks all norm-square margins, midpoint product
rounding, propagated radii, the signed sum and final margin. It rejects
zeroed interior norm bounds and a zeroed midpoint error radius. A formatting
issue initially split a real type annotation across lines; the reader now
normalizes whitespace in type annotations before parsing arithmetic. No
numeric payload or Lean statement changed for that reader correction.

Final acceptance:4546build jobs,65declarations with exactly propext,
Classical.choice and Quot.sound,735matching dependency sources/configuration,
no new-module warnings, regeneration and independent arithmetic passed.

Next steps

1. Certify the original fourth-envelope numeric expressions with the actual
   support-crossing near/far geometry; the2548 direct-price probe supports
   this choice without additional inverse-deficit capping machinery.
2. Assemble the coefficient-weighted third bound, curvature and both signed
   order-zero endpoint values into the boundary-cell integral consumer.
3. Extend verified cell coverage and pricing to batches while retaining
   exact coefficient membership and the complete signed budget as separate
   unresolved obligations.

Evidence

results/2549_boundary_bounds_readback.json
ConnesWeilRH/Dev/C1RouteABoundaryLeftBounds2549.lean
ConnesWeilRH/Dev/C1RouteABoundaryRightBounds2549.lean
ConnesWeilRH/Dev/C1RouteABoundaryMidpointBounds2549.lean
scripts/generate_boundary_bounds_2549.py
scripts/validate_boundary_bounds_2549.py
