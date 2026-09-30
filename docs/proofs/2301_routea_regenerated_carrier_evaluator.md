# Record 2301: implemented regenerated evaluator and execution-model price

## Result and evidence

The regenerated 768:6 evaluator clears the sampled transform-bridge method
price on all three grids. The finest-grid charge is 1027592.41478698, or
0.10275924 times the 1e7 budget. Unlike record 2300's ideal-geometry variant,
this is an implemented evaluator with separate coefficient, geometry,
oscillatory evaluation, accumulation and final-cast prices.

This is a round-to-nearest execution-model price, not a formal machine proof
or continuous-integral certificate. The artifact keeps certificate=false and
hgap_closed=false. Evidence: `results/2301_regenerated_carrier_evaluator.json`
and `scripts/routea_regenerated_carrier_evaluator_2301.py`.

```text
grid step | sampled method charge | ratio to 1e7
----------+-----------------------+-------------
0.020     | 1027029.88983032      | 0.10270299
0.010     | 1027537.47219713      | 0.10275375
0.005     | 1027592.41478698      | 0.10275924
```

All 30 captured families, both coefficient hashes, 25 carrier groups and
41136 prime powers remain unchanged. The ideal coefficient intervals are
regenerated from the exact degree-six Lobatto cosine matrix. Their binary64
cast charges reproduce record 2300's complete base/correction readings
exactly. No owner coefficients are re-solved.

## What changed and why

The physical panel coordinates use the tested WSL extended format, whose
significand has 64 binary bits, rather than binary64's 53. The NumPy type
label float128 must not be interpreted as 128 bits of precision. A stored
extended number is lifted to an exact rational via as_integer_ratio before
its deviation from ideal geometry is charged.

A phase is the angle of the rotating complex factor exp(-i x). A moment is
the integral of a monomial t^k against that factor on [-1,1]. Instead of
calling unpriced trigonometric functions or dividing by a near-zero frequency,
the evaluator uses real Horner polynomials for cosine, sine and the moments.
Horner evaluation builds a polynomial from its highest coefficient downward,
requiring one multiplication and one addition per stage.

The degree-six moments use the first 48 exponential-series terms. Even
moments are real; odd moments are imaginary. Phase arguments are reduced by
an integer multiple of twice the represented pi before the same series is
evaluated. Pi representation, frequency formation, reduction arithmetic,
series coefficient conversion and series truncation are all separately
included in the model. The moment domain is checked analytically over the
whole frequency window, not merely at sampled nodes; its bound is below 3.
The reduced-phase domain is also bounded analytically under the declared
rounding model: nearest-integer reduction gives a half-period plus explicitly
charged division, multiplication and subtraction errors. Its full-window
bound is below 3.2, in addition to the runtime range gates.

The 19200 panel/carrier contributions use a streaming balanced summation
tree of depth 15. This limits the number of rounding stages along a term's
path, rather than claiming cancellation makes summation exact. A final
binary64 complex cast is also charged.

## Bound assembly

Let u = 2^-64 be the model's extended unit roundoff, and
gamma_n = n u/(1-n u) its n-step relative inflation. The real series path
uses an operation allowance of 208; the complex coefficient/moment/phase
post-chain uses 96. These are declared conservative operation-count
assumptions, not consequences of the numerical controls alone.

Let p bound phase-value error and let m bound moment error after dividing
by 2/(k+1). Let M be the sum of panel radii times coefficient magnitudes
weighted by 2/(k+1). Each carrier coefficient retains the full complex
modulus. The execution radius is

R_exec = M (p + m + p m + gamma_96 (1+p)(1+m)).

The sum radius is sqrt(2) gamma_15 (1+gamma_96)(1+p)(1+m) M.
The final cast uses the resulting safe magnitude, not the measured
possibly-cancelled output. Nonzero underflow allowances are retained. The
cross product p m is not dropped.

```text
transform bridge term | base radius       | correction radius
----------------------+-------------------+-------------------
interpolation         | 3.36711709e-14    | 6.11635156e-11
coefficient cast      | 2.25246744e-15    | 3.61773492e-12
extended geometry     | 9.61452999e-17    | 1.51281353e-13
execution model       | 9.38767273e-14    | 1.52445285e-10
pairwise accumulation | 6.16722901e-17    | 1.00148888e-13
final binary64 cast   | 8.42032335e-15    | 1.36736615e-11
----------------------+-------------------+-------------------
combined              | 1.38378507e-13    | 2.31151627e-10
```

## Independent controls and nonclaims

The independent full-polynomial reference uses 100-digit quadrature for the
moments and direct high-precision exponentials, integrating the regenerated
stored coefficients at their represented coordinates. Ten channel/point
checks cover both window ends, both signs of 3.605 and zero. The maximum
execution-allowance ratio is 0.0005759913. These controls verify execution
consistency, not the bump interpolation theorem or selected-owner identity.

Nine selftests cover exact extended lifting, both phase signs, both moment
parities, injected pi error, pairwise error allowances, chunk-size invariance,
rejection of an inadmissible full-window moment range, the complete charge
ledger, and source provenance. Injected pi error exercises error-input
propagation rather than only exact-input evaluation.

The rounding mode is smoke checked, not formally proved. The operation-count
model still needs source-level certification. Kernel/annihilator evaluation,
functional multiplication and trapezoid arithmetic are outside this transform
bridge. Continuous integration, infinite tails and actual selected-owner
readback remain open. There is no hgap supplier, producer GO or RH claim.

The next named task is a continuous finite-window price, with local frequency
Taylor bounds for the regenerated polynomial transforms and explicit remainder
charges. A Taylor bound approximates a function on a small interval while
keeping a bound on what was omitted. This must preserve cancellation by
forming the full complex carrier sum before taking magnitudes. Another global
amplitude bound or grid-agreement claim is not a substitute for that obligation.
