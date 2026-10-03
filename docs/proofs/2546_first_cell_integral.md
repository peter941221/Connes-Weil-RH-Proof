Record 2546: first numerical whole-cell integral

The target is production cell 5440 of the 10240-cell grid, sigma = +1/2,
with the same 30 functions, squared stored widths, signed modulation and
record-2338 coefficient centers/radii. The numerical upper is
379207837/500000000000 = 0.000758415674.

The theorem cellIntegralBound2546 retains the premise that each actual
coefficient lies within its specified radius of the stored center. It
bounds the integral of the complex function's norm over the whole cell.
It does not assert exact-owner coefficient membership, full-grid coverage,
selected-owner positivity or RH.

Assembly

The left signed order-zero bound is reused from record 2542. The right
endpoint is generated with the same adaptive evaluator at index 5441,
giving 6061937461/10000000000. The reused generator retains its 2542
declaration suffixes inside the new CellRight2546 module; these are new
index-5441 declarations, not reuse of a bound at another position.

For each family, the maximum of its two certified third-derivative endpoint
norms is increased by half the cell width times its certified fourth
envelope. Its coefficient charge uses the sum of absolute real/imaginary
center coordinates plus 10^-30. Each resulting charge is rounded upward
to a multiple of 10^-6. This yields the aggregate third upper
1237907300787/250000. Combining it with the signed midpoint bound yields
the curvature upper 5663644581/1000000.

The existing record-2539 integral theorem combines the two endpoint values
and the curvature charge. Thus the numerical payload acts on the entire
cell, including points between the evaluated nodes. The signed center
sum remains intact in the endpoint and midpoint values; scalar magnitude
bounds are used for the derivative-variation allowance.

Validation

The independent reader replays the right-node exact exponential and signed
sum arithmetic, all fourth-envelope bounds and the endpoint norm margins.
It then checks the coefficient products, upward per-family charges, third
sum, curvature bound and final integral inequality using rational numbers.
It rejects an integral upper replaced by zero. Generator regeneration,
Lean build, allowed-axiom audits and dependency-source identity are separate
acceptance gates, recorded in results/2546_cell_readback.json.

Final acceptance passed: 4549 build jobs, six audited terminal declarations
with exactly propext, Classical.choice and Quot.sound, 738 byte-identical
dependency sources and matching build configuration. Independent rational
readback and regeneration passed, with no new-module warnings.

The initial assembly needed explicit a and b arguments in the call to the
generic cell-integral theorem. Supplying the exact endpoint definitions
fixes inference without altering the bound or coefficient premise.

Next steps

1. Price batched certificate verification and cover representative difficult
   cells before extending to both signs and all 10240 cells. Completion
   requires actual cell certificates, not sampled curvature surrogates.
2. Establish that the exact interpolation coefficients belong to the imported
   coefficient ranges. This removes the outstanding membership premise.
3. Assemble the remaining channels and same-owner signed budget. A positive
   outcome must concern the selected detector and discharge the actual
   producer obligation before any RH claim.

Evidence

ConnesWeilRH/Dev/C1RouteACellIntegral2546.lean
ConnesWeilRH/Dev/C1RouteACellRight2546.lean
scripts/generate_cell_integral_2546.py
scripts/validate_cell_integral_2546.py
results/2546_cell_readback.json
