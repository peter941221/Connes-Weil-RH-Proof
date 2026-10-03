Record 2545: numerical fourth-derivative envelope on cell 5440

The target is fourthCellTerm2544 for each of the unchanged 30 families,
at sigma = +1/2 and endpoint indices 5440/5441. The new factorization
is an equality of the existing 2538 envelope, not a replacement function
or a sampled fourth derivative.

The exponential weight and bump decay are combined before evaluation.
Writing t = 1/(1-near^2), the scalar exponential is exp(b/2 - 30*t).
The remaining factor is the finite order-four sum with the absolute bump
polynomial, powers of t, powers of the radius, binomial coefficients and
the norm of sigma + i*modulation. This preserves the coupled decay at
the support edge. For this cell, all 30 families have 0 < near < far < 1.

The exponential uses the already proved compact rational evaluator.
The squared frequency norm is bounded by a rational upward square root.
The final product is rounded upward to the 2^-100 grid and verified in
Lean. The generator reuses the scalar evaluator with zero imaginary
argument; that scalar calculation does not change the signed modulation
of the owner, which remains in the frequency norm.

Independent arithmetic validation derives the bump polynomials by the
recurrence P_(k+1) = (1-u^2)^2 P_k' + 4k*u*(1-u^2)*P_k - 60u*P_k,
starting at P_0 = 1. It takes absolute polynomial coefficients only
after this derivation. It independently replays rounded exponential
arithmetic, verifies the exponent against exact grid/support geometry,
checks the frequency square and final rational product, and rejects a
zeroed final upper. Regeneration is a separate check.

Implementation corrections

The generic proof needs an explicit even-power nonnegativity argument:
the inverse support deficit need not be assumed positive in that algebraic
lemma. The numerical geometry does certify positivity for this cell.
The real exponent is named before coercion to complex, preventing the
printer's nested rational casts from hiding the real-exponential norm
identity. Nat.choose is explicitly evaluated in the finite polynomial.
None of these corrections changes the mathematical bound.

Scope

Exact-rational assembly pricing uses the L1 magnitude of each complex
coefficient center plus its 10^-30 radius. The endpoint third contribution
is 4748202.798049299 and the fourth variation contribution is
203426.40508653925. Together with the accepted midpoint upper this gives
a prospective curvature upper 5663.64458086269 and an integral curvature
charge 9.897936753129368e-7. These decimal displays come from exact
rationals in results/2545_cell_curvature_price.json. The corresponding
aggregate inequality has not yet been imported into Lean, so these
figures are assembly planning, not a formal cell-integral claim.

Even acceptance of all 30 fourth envelopes does not by itself establish
a numerical cell integral. Their coefficient-weighted aggregate, the
right signed order-zero endpoint and the final cell arithmetic must be
connected. Full-grid certification, exact coefficient membership,
correction channels and selected-owner positivity remain open.

Evidence

Final acceptance: 4546 build jobs, 34 audited 2545 declarations with
exactly propext, Classical.choice and Quot.sound, 735 byte-identical
project dependency sources and matching build configuration. All 30
independent rational replays passed; no new-module warnings remained.
The largest individual exported fourth bound is approximately
3.063951997716959e-6 before multiplication by coefficient magnitudes.

ConnesWeilRH/Dev/C1RouteAFactoredCellEnvelope2545.lean
ConnesWeilRH/Dev/C1RouteAFourthEnvelope2545.lean
scripts/generate_fourth_envelope_2545.py
scripts/validate_fourth_envelope_2545.py
results/2545_fourth_readback.json
