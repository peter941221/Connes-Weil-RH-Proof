Record 2543: signed midpoint second-derivative certificate
Date: 2026-10-04

The signed cell-integral consumer in record 2539 needs an order-two value
at the actual cell midpoint, plus a whole-cell order-three bound. The latter
is supplied analytically by 2538 but still requires numerical endpoint
order-three bounds and a numerical order-four envelope. Pointwise midpoint
certificates alone do not close this whole-cell obligation.

Exact factorization

Let x be position, r the positive squared stored width, sigma the endpoint
parameter, and theta the signed modulation. Define u=x/r and q=1-u^2.
Inside the support, the unit-family function is

```text
f(x) = exp(sigma*x - 30/q + i*theta*x).
lambda = sigma + i*theta.
P_0(u) = 1.
P_1(u) = -60*u.
P_2(u) = -60 + 3480*u^2 + 180*u^4.
B_k(x) = P_k(u) / (r^k * q^(2*k)).
M_n(x) = sum_(j=0..n) choose(n,j) * lambda^j * B_(n-j)(x).
f^(n)(x) = M_n(x) * f(x), n <= 4.
```

P_3 and P_4 are the existing signed polynomials in bumpNumerator2350;
the implementation does not replace them by their absolute coefficient
envelopes. The factorization follows from the already-proved bump derivative
ladder and the weighted product rule. Outside the support, including its
boundary, the actual derivative is zero for every order.

Given an approximate value c with |f-c| <= e and |M_n| <= L, the new
complex_multiplier_error2543 proves |M_n*f-M_n*c| <= L*e. This retains
the complex multiplier in the center; only its error contribution uses L.

Concrete midpoint

The generated certificates use the midpoint of production cell 5440 on
the exact 10240-cell grid, with sigma=+1/2 and all 30 original families.
midpoint_grid2543 identifies the point with the arithmetic mean of the two
actual grid endpoints. Each certificate checks its scaled argument, the
rounded exponential computation, the original owner exponent, and the
exact order-two multiplier before applying the error-transfer theorem.

The final signed-aggregate build and root integration pass: 4540 jobs,
40 audited declarations with exactly the three standard axioms, and 729 project sources matching the
build mirror byte-for-byte. Toolchain/config identity and regeneration also
pass, with no new-module warnings. These 729 files are the dependency closure
of this audit and the root, not a count of all repository files.

The independent reader checks the factor by a different formula. Let a be
the first derivative of the exponent and b its second derivative:

```text
a = sigma - 60*x/(r^2*q^2) + i*theta.
b = -60/(r^2*q^2) - 240*x^2/(r^4*q^3).
M_2 = a^2 + b.
```

It reconstructs both rational coordinates, independently replays the
exponential arithmetic, and rejects a deliberately zeroed factor. The
30-family signed aggregate now has the concrete Lean upper
997840737/400000 = 2494.6018425, including evaluation, rounding and
coefficient-box uncertainty. The theorem signedMidpointUpper_le2543 bounds
signedJetUpper2539 at order two with the unchanged 2540 midpoint coefficients
and errors. Its actual-coefficient consumer retains box membership as a premise.

Signed assembly and rounding

Multiplying each exact rational derivative factor by its rational exponential
center produces large denominators. Each product is rounded to the existing
2^-100 coordinate grid, with scalar error at most 2^-99. The final radius is
the upward 2^-140 rounding of the multiplier magnitude times the exponential
error, plus this new rounding charge. Lean checks the rounded computation
with cbv and propagates both errors by the triangle inequality.

The exact signed sum of the 30 rounded complex centers is formed before
taking its norm. Its norm is bounded by 2494.6018424. The exact weighted
evaluation/rounding charge is approximately 5.677928522352508e-11, and Lean
uses the larger allowance 1e-8. Each actual unit-family second derivative
has norm at most one at this midpoint, so coefficient uncertainty costs at
most 30e-30. The final 1e-7 margin covers both charges.

Independent readback checks every rounded product and upward radius,
the signed total, the squared-norm inequality and the final margin. A
zeroed radius and a changed rounded center must both be rejected. The first
build used the two-argument norm_sub_le as if it were a three-point triangle
bound; an explicit identity plus norm_add_le fixes that interface error
without changing the data or allowance.

Precision pricing

The bounded external probe tests midpoint cells 5120, 5440 and 10239 at
both endpoint signs and orders two/three. Its trial local evaluation-error
allowance is 1e-8. All sampled order-two charges pass; the largest is
approximately 1.738e-13 after multiplying by h^3/12, where h is cell width.

At the edge midpoint, the order-three error is about 238718; multiplying
by h^4/24 gives 2.670e-8, above the trial allowance. This does not refute
the function bound or prove failure of the global budget. It rejects blind
reuse of fixed precision under this local allowance. The order-three
midpoint reading is not an endpoint or supremum certificate; h^4/24 is
only its hypothetical coefficient in a third-cell charge.

Next steps

1. Price and certify actual order-three endpoints and the coupled order-four
   whole-cell envelope. Higher-order precision must be chosen from these
   actual charges, not from the order-zero pilot.
2. Combine these certificates through the existing cell-integral consumer,
   retaining exact coefficient membership as a separate obligation.
3. Extend the accepted cell architecture to the remaining grid and the
   other endpoint parameter before claiming a full-strip numerical bound.

Full-grid integration, exact coefficient membership, correction channels,
selected-owner positivity and RH remain open.

Evidence:
ConnesWeilRH/Dev/C1RouteADerivativeMultiplier2543.lean
ConnesWeilRH/Dev/C1RouteAMidpointDerivatives2543.lean
scripts/routea_derivative_pricing_2543.py
scripts/validate_midpoint_derivatives_2543.py
results/2543_derivative_pricing.json
results/2543_midpoint_readback.json
ConnesWeilRH/Dev/C1RouteASignedMidpoint2543.lean
scripts/generate_signed_midpoint_2543.py
