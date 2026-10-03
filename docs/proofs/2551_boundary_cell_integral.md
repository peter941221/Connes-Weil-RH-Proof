Record2551: complete numerical integral for support-crossing cell2700

The same30-family owner at sigma+1/2 now has the cell-integral upper
57/500000000000 = 1.14e-10 on production cell2700. The theorem
boundaryCellIntegralBound2551 explicitly retains membership of the actual
coefficients in the imported coefficient balls. It covers all points of
this cell, not merely evaluated endpoints or the midpoint.

This cell exercises support crossing: six families are active at the left
endpoint,28at the right and midpoint;22cross a support boundary inside
the cell. Exterior derivatives are proved exactly zero. Interior derivative
evaluation uses the160-bit engine proved in2547. The original fourth
envelope and its support split are retained without inverse-deficit capping.

Numerical chain

The order-zero endpoint uppers are179/2000000000 on the left and
873/10000000000 on the right. They use the existing100-bit adaptive
evaluator with all errors charged; the stronger precision is needed for
the derivative multipliers, not automatically for every channel.

The signed midpoint second-derivative upper is8777/50000000. Thirty
coefficient-weighted endpoint/fourth allowances, rounded upward to1e-6,
give third aggregate4373/500000 = 0.008746. The resulting curvature upper
is91/500000 = 0.000182. The existing2539cell-integral theorem combines
this curvature charge with both endpoint values; the final upper rounds
upward to a multiple of1e-12.

The template wrapper uses the same accepted per-family and integral
inequalities as2546. Its local term is already a fully numerical expression,
so that term's proof is direct rational evaluation. The previous2546
generator's default output remains byte-identical.

Validation

Independent readback checks both actual adaptive endpoint payloads, all
fourth-envelope entries and geometry, endpoint norm margins, the signed
midpoint arithmetic, coefficient products, per-family rounded charges,
aggregate, curvature and final integral. Replacing the final integral
upper by zero is rejected. Regeneration, Lean build, allowed-axiom audits
and dependency-source identity are separate acceptance checks recorded in
results/2551_boundary_integral_readback.json.

Final acceptance passed: 4557 build jobs, eight terminal declarations with
exactly propext, Classical.choice and Quot.sound, 746 byte-identical project
dependency sources and matching build configuration. No new-module warnings
remained; independent arithmetic, regeneration and corruption rejection passed.

Scope and next steps

Two individually completed production cells,5440and2700at sigma+1/2, do
not establish a full-grid estimate. Remaining cells and the other sign,
exact coefficient membership, correction channels and the complete
selected-owner signed budget remain open. The current route ruling is
unchanged, and no RH claim follows from this milestone.

The next scaling step is to parameterize batch generation with explicit
support branches and measure verification cost on more than one cell.
Grid replication must be based on that control, not source-size reduction
or a single warm build time.

Evidence

ConnesWeilRH/Dev/C1RouteABoundaryIntegral2551.lean
ConnesWeilRH/Dev/C1RouteABoundaryValueLeft2551.lean
ConnesWeilRH/Dev/C1RouteABoundaryValueRight2551.lean
scripts/generate_boundary_integral_2551.py
scripts/validate_boundary_integral_2551.py
results/2551_boundary_integral_readback.json
