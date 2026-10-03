Record 2560: production-grid pricing and a two-channel strip consumer

The production-grid arithmetic fits the existing base-norm pin at both
signs. Separately, a new Lean theorem reduces the frozen-strip consumer
from four endpoint-bound channels to two. The full-grid numeric table is
external evidence; the new consumer reduction is kernel-checked. Neither
result closes coefficient membership or the selected-owner signed budget.

The concrete target

C1RouteAEndpointStrip defines baseNormUpper2343=2.7790943782. The base
function's weighted norm must be at most this value at sigma=-1/2 and +1/2.
Record 2539 proves the analytic grid-to-integral inequality, and records 2546
through 2559 provide actual cell certificates. Pricing must therefore use
the current cell generator's constants, not substitute the older 2535 Arb
table or a sampled integral.

The new replay uses exact FLINT rationals for all 10240 cells at each sign.
It reproduces the 160-bit exponential centers and 200-bit error radii,
100-bit midpoint-product rounding, 40-bit frequency upper, 160-bit endpoint
norm upper, coefficient L1 upper plus 1e-30, 1e-6 per-family third charges,
1e-6 curvature rounding and 1e-12 final cell rounding. Signed sums are formed
before their complex norm. The coefficient L1 upper is only used where the
production third-derivative allowance already uses that upper.

```text
+-------+----------------+----------------+----------------+
| sigma | candidate sum  | required pin   | remaining room |
+-------+----------------+----------------+----------------+
| -1/2  | 2.688485658169  | 2.779094378200  | 0.090608720031  |
| +1/2  | 2.676776836740  | 2.779094378200  | 0.102317541460  |
+-------+----------------+----------------+----------------+
```

These decimals are exact rationals. The row-by-row upper-rounding cost is
about 6.14e-9 per sign. Evaluation-charge gates pass at every endpoint and
midpoint. Thus the current rounding schedule does not exhaust the base
budget; full-grid formal replay remains worthwhile at unchanged constants.

Eight accepted Lean cell certificates reproduce exactly at the third,
curvature and integral levels. There are 960 exact center/error/depth/factor
comparisons against the original Fraction-based evaluator and polynomial
derivative engine, covering zero, interior and exterior positions. Two
independent spans match between sequential and multiprocessing execution.
The full reader checks 20480 ordered rows, shared endpoints, charge gates,
curvature and quadrature arithmetic, rational totals and source hashes. A
zeroed central-cell integral is rejected. These checks are not a Lean import
of the unproved grid nodes.

The four-worker run took 42.48 s for both signs, using python-flint 0.9.0 in
the Linux verification environment. This measures exact numeric pricing,
not Lean verification cost. Generate with scripts/price_production_grid_2560.py
using --workers 4. Validate with
scripts/validate_production_grid_2560.py and --price pointing to the result.

The smaller consumer obligation

Write N(b) for the weighted integral of the norm of the base function b,
and D(c) for the weighted integral of the norm of the second derivative of
the correction function c. The existing consumer is

    min(D(b)*N(c), D(c)*N(b)) <= B,

where B=9506275.102584327. Since the minimum is at most its second entry,
it suffices to prove N(b)<=2.7790943782 and D(c)<=666472.585392 throughout
the centered strip. Their product is exactly

    578809442277289576017/312500000000000,

approximately 1852190.2152873266, below the unchanged B. The existing
endpoint-to-strip theorem extends each of these two bounds from the two
endpoint signs to every sigma in [-1/2,1/2]. No separate bound on D(b) or N(c)
is needed for this sufficient route. Those bounds may remain useful in other
arguments; the new theorem does not assert them.

frozenStripHypothesis_of_two_external_endpoint_bounds2560 retains the same
base and correction coefficient functions, signed modulation function and
existing external-to-physical identities. It concludes the original
FrozenStripHypothesis and introduces no substitute object or positivity
assumption. Its two endpoint inputs remain explicit hypotheses.

Lean validation passed 4378 build jobs and all three terminal declarations
use exactly [propext, Classical.choice, Quot.sound]. The 602 project dependency
sources and toolchain configuration match the verification environment
byte-for-byte, and the new module has no warnings.

Remaining work

1. Turn the base grid's successful numeric price into full kernel-checked
   coverage and its finite sum. The external table alone does not do this.
2. Certify the correction second-derivative endpoint bounds at both signs.
   Its integrand is exp(sigma*x)*|c''(x)|, not |(exp(sigma*x)*c(x))''|;
   those expressions contain different sigma terms.
3. Prove actual interpolation-coefficient membership and complete the other
   healthy-owner and signed-kernel obligations. The two-channel reduction
   removes only the extra norm channels at this strip-budget interface.

Evidence: ConnesWeilRH/Dev/C1RouteATwoChannelStrip2560.lean,
results/2560_production_grid_price.json and
results/2560_production_grid_validation.json.
