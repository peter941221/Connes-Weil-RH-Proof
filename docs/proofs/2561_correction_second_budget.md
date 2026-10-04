# Record 2561 — Correction second-derivative strip norm priced under its pin

Verdict: PASS at both endpoint signs, external exact arithmetic. The enclosure
of integral exp(sigma*x)|c''(x)| dx over the production support stays below
41654536587/62500 = 666472.585392 with margin above 5.4e5 at each sign. This
prices the second channel of the 2560 two-channel bridge. It is not a Lean
certificate, does not prove coefficient membership, and does not feed
producer_go.

## Target and convention

The channel quantity is integral exp(sigma*x)|c''(x)| dx, where c is the
correction function built from the 2338 ideal_correction_coefficient boxes and
the 2275 owner capture. Differentiating the weighted function exp(sigma*x)c(x)
instead produces extra sigma terms and answers a different question; the
independent controls detect that wrong convention and the priced quantity
excludes it.

Each family jet satisfies jets[k] = (d/dx)^k [exp(sigma*x) c''(x)]. The
polynomial ladder extends the 2535 bump numerators two orders further (order
6) and asserts result[:5] == base.POLYS, so the first five polynomials are the
already-certified ones.

## Enclosure structure

Same skeleton as the certified 2535 base enclosure:

- Nodes: signed center sum plus per-family coefficient error, cancellation
  preserved before taking the modulus (center-plus-scalar-error).
- Per cell: trapezoid node terms h/2(|F(a)|+|F(b)|) plus remainder
  h^3/12 * curvature, where curvature bounds |F''| across the cell through
  |F''(midpoint)| + (h/2) max|F'''|, and max|F'''| adds the growth allowance
  (h/2) max|F^(4)| from a whole-cell fourth-derivative envelope.
- The envelope keeps the coupled decay-growth product: decay exp(-30t) at the
  cell point nearest zero (t = 1/(1-u^2) is increasing on the support, so the
  nearest point maximizes exp(-30t)t^(2j)), polynomial growth at the point
  farthest from zero clamped at the support edge, and exp weight at
  max(sigma*a, sigma*b). Families evaluate to exact zeros outside their
  support radius.
- Coefficient error enters the growth allowance through
  scale = upper(|center| + error), the same charging as 2535.
- exact_upper keeps the 2^-128 positive floor from 2535, so flat support
  edges never round to zero or serialize enormous denominators.

All arithmetic runs on python-flint arb/acb balls at precision 192 plus exact
Fraction node sums. 10240 cells per sign, full run 40.1 s.

## Results

Pin: 41654536587/62500 = 666472.585392.

| sigma | node sum       | remainder  | total upper    | margin         | fits |
|-------|----------------|------------|----------------|----------------|------|
| -1/2  | 125446.7113... | 935.0256...| 126381.7369... | 540090.8484... | yes  |
| +1/2  | 100361.7612... | 928.7910...| 101290.5522... | 565182.0331... | yes  |

Exact totals live in results/2561_correction_second_10240.json as Fractions;
the columns above are their decimal reads.

Two-channel consequence (still external inputs, pairing signs):

| sigma | N(b) upper (2560) | D(c) upper (2561) | product      | budget 9506275.1026 |
|-------|-------------------|-------------------|--------------|---------------------|
| -1/2  | 2.688485658169    | 126381.7369...    | ~339775.5    | fits, ~28x headroom |
| +1/2  | 2.676776836740    | 101290.5522...    | ~271132.2    | fits, ~35x headroom |

## Verification scope

- 90 derivative controls: independent mpmath numerical differentiation of the
  atom against the priced jets at 3 families x 2 signs x 3 points x 5 orders;
  max scaled relative error 5.30e-56 against the 1e-45 bar.
- 90 envelope sample checks: |F^(4)| at interior samples of three cell shapes
  per family and sign, including support-crossing cells, all at or below the
  envelope.
- Wrong-convention control: d^2/dx^2[exp(sigma*x)atom] differs from
  exp(sigma*x)atom'' beyond 1e-8 relative at the sampled points, so the
  controls can tell the two apart; the priced target is the second one.
- Endpoint and exterior jets are exactly zero at |x| >= r.
- Remainder scaling ladder 256/512/1024/2048/4096 cells: successive doubling
  ratios 12.02, 10.42, 9.34, 8.67 converge to the h^3 remainder law, each a
  steady 3-4% above 8. Pure h^3 from 4096 predicts 968.1 at 10240 against
  935.03 observed, continuing the same slight extra decay seen at every
  ladder step. A single 256-cell smoke run extrapolated under the naive h^2
  law looks 100x too large; the ladder rules out an edge anomaly before
  acceptance.
- The engine imports the certified 2535 module unmodified and
  load_families re-verifies the 2338 capture sha256 before pricing.

## Remaining obligations

- No Lean certificate covers this grid sum; the 640,940-active-exponent
  scaling problem from record 2553 still gates formal coverage.
- Coefficient membership: the priced c uses the 2338 ideal_correction_coefficient
  boxes as its coefficient universe; proving the actual interpolation
  coefficients lie inside them remains open.
- The two-channel product theorem keeps both endpoint inputs as explicit
  hypotheses; this record supplies candidate values for one of them, not a
  proof.
- The selected-owner signed budget, the remaining correction terms, and the
  final positivity question all stay open. Nothing here supports an RH claim.

Evidence: results/2561_correction_second_10240.json,
results/2561_correction_controls.json, ladder files
results/2561_correction_second_{256,512,1024,2048,4096}.json,
scripts/price_correction_second_2561.py,
scripts/validate_correction_second_2561.py,
build-logs mirror 2561_controls.log and 2561_full_grid.log.
