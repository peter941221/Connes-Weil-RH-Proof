# 2349 - Exact bump derivative recurrence and same-node repricing

Date: 2026-10-01

Result: positive for the norm-supplier obligation, not for the selected Weil
sign. An exact integer recurrence gives smaller safe derivative constants
through order four. The external continuum min-product upper falls from
1852190.2152630097 to 1808469.1730280858, a 2.3605% reduction. It occupies
0.6838494494 of the unchanged 2644542.8515 pin. The new Lean module proves
the scalar envelope needed by the recurrence, not the complete derivative
identity or numerical endpoint facts.

## What is bounded

A bump is a smooth function that is exactly zero outside a finite interval.
Here the interval radius is R > 0, the physical coordinate is x, and the
normalized coordinate u = x/R satisfies |u| < 1 in its interior. Set
q = 1-u^2 and t = 1/q. Thus q > 0 and t >= 1. The unmodulated bump is
f(u) = exp(-30/q). The constant 30 is the actual owner's decay parameter.

A derivative measures how fast a function changes. Panel integration of a
function needs a second-derivative bound; integrating its second derivative
needs orders two through four. An upper bound on these derivatives is a
majorant: a ceiling valid at every point, not a value observed at samples.

```text
2349: exact polynomials + scalar envelope
                    |
                    v
owner coefficients + radii + modulation -> derivative ladder
                    |
                    v
2347/2348 chord bound + unchanged 2342 node sums
                    |
                    v
external norm upper; NOT the selected signed functional

disconnected formal obligations:
  derivative identities -> actual owner -> numeric node import
```

## Exact derivation

Write f^(n)(u) = exp(-30/q) q^(-2n) P_n(u), with P_0 = 1.
Here n is the derivative order and P_n is an integer-coefficient polynomial.
Differentiating the product gives the recurrence

P_(n+1) = q^2 P_n' + (-60u + 4nuq) P_n.

The term -60u comes from differentiating the exponential; 4nuq comes from
differentiating q^(-2n); q^2 P_n' comes from the polynomial. Expanding and
combining like powers BEFORE taking absolute values preserves exact algebraic
cancellation. The independently generated numerators are:

```text
P_0 = 1
P_1 = -60u
P_2 = -60 + 3480u^2 + 180u^4
P_3 = 10080u - 193680u^3 - 31680u^5 - 720u^7
P_4 = 10080 - 1085040u^2 + 10189440u^4
      + 3575520u^6 + 266400u^8 + 3600u^10
```

For |u| <= 1, |P_n(u)| is no larger than the sum of its absolute
coefficients. For t >= 1 and m <= 30, log(t) <= t-1 gives

m log(t) - 30t <= m(t-1) - 30t <= -30,
so t^m exp(-30t) <= exp(-30).

Use m = 2n, which is at most 8 here. Therefore the bound for the nth
physical derivative is C_n exp(-30) / R^n, where C_n is the absolute
coefficient sum. For a small example, u = 0 gives f''(0) = -60 exp(-30),
well below the ceiling 3720 exp(-30). This ceiling is deliberately not tight.

```text
+-------+-----------------+-----------------+
| order | legacy C_n      | derived C_n     |
+-------+-----------------+-----------------+
| 0     |               1 |               1 |
| 1     |              60 |              60 |
| 2     |            3900 |            3720 |
| 3     |          245160 |          236160 |
| 4     |        23402880 |        15130080 |
+-------+-----------------+-----------------+
```

The coarser two-variable recurrence treats u and t independently. It gives
272160 at order three, but this is NOT evidence that 245160 is invalid.
After substituting t = 1/(1-u^2), the exact polynomial ceiling is 236160,
which is below 245160. All legacy constants are dominated by the newly
derived ceilings; no old constant is declared unsound.

The second exact recurrence is
A_(n+1) = dA_n/du + 2u t^2 dA_n/dt - 60u t^2 A_n.
Clearing its denominator q^(2n) reproduces every P_n exactly with Python
integers. This is an independent algebraic implementation, not a second
formal proof checker. Independent mpmath differentiation also agrees at
both signs and the cancellation centre. These controls test implementation;
they do not replace the all-points mathematical argument above.

## Same-owner pricing

For a family c exp(i theta x) f(x/R), c is its complex coefficient and
theta its real oscillation frequency. The product derivative rule gives

M_n = sum_families |c| sum_(i=0..n)
      binom(n,i) |theta|^i C_(n-i) exp(-30) / R^(n-i).

No coefficient, radius, frequency, support, grid or pin is changed.
The 2338 ideal coefficient rectangles and exact captured width-square radii
are loaded through the existing hash-checked source loader. The new run
reuses the eight directed node-sum uppers from the 120001-node 2342 artifact;
it does NOT rerun those nodes. A directed upper is arithmetic rounded outward
so it cannot knowingly fall below the quantity it encloses.

In the same run, the original panel terms and endpoint totals reproduce
exactly at 192-bit precision before any new price is accepted. Every new
panel and total is smaller. The three terms controlling panel curvature
remain M_(n+2) + 2|sigma|M_(n+1) + sigma^2 M_n, multiplied by
exp(|sigma|R) h^2 (2R)/12; sigma is the real exponential weight and h is
the exact uniform grid step.

```text
+----------------------+--------------------+--------------------+
| endpoint maximum     | 2342               | 2349               |
+----------------------+--------------------+--------------------+
| base norm            |       2.7790943782 |       2.7785828360 |
| base second norm     |    9044.9434471792 |    9035.2117827318 |
| correction norm      |     231.2642026141 |     230.4091658001 |
| correction second    |  666472.5853917701 |  650860.2693435578 |
| min-product upper    | 1852190.2152630097 | 1808469.1730280858 |
| upper / frozen pin   |       0.7003820015 |       0.6838494494 |
+----------------------+--------------------+--------------------+
```

The table is a display, not the certificate. Exact rational upper endpoints
are in results/2349_derivative_ladder.json. Existing 2343 rounded interface
constants are unchanged; this record does not silently import smaller numbers
into that Lean consumer.

## Formal verification and scope

C1RouteABumpEnvelope.lean proves:

1. powerExpUpper2349: t^m exp(-decay*t) <= exp(-decay) whenever
   t >= 1 and m <= decay.

2. polynomialAbsUpper2349: a finite polynomial on |u| <= 1 is bounded
   by the sum of absolute coefficients.

3. polynomialExpUpper2349: combines those two ceilings, with decay 30.

The focused Linux build completes 2943 build-plan jobs. All three audit
leaves have exactly [propext, Classical.choice, Quot.sound], with no new
source warnings. These are the permitted logical foundations, not added
mathematical assumptions. The Mathlib/plausible/LeanSearchClient local-change
warnings pre-exist and are not attributed to the new module.

The complete order-three/four derivative identity and the coefficient-sum
instantiation are NOT formalized by this module. The record therefore leaves
derivative_majorants_formalized_in_lean false. No Python evaluator semantics,
finite-node facts, repaired coefficient realization, healthy detector,
complete signed-kernel budget, producer GO, or RH claim is imported or made.
A norm is a size; the selected Weil sign is a signed balance. A better size
ceiling alone cannot turn that balance into a nonnegative one.

## Validation

- 12 new tests pass, covering exact polynomial coefficients, two-variable
  recurrence, independent mpmath derivatives, both-sign envelope samples,
  invalid radii and lengths, grid/endpoint/scope/provenance mutations,
  identical replay, unchanged node sums and exact product reconstruction.
- 15 unchanged 2342 regression tests pass.
- Separate command replay is byte-identical. It replays the cheap panel
  calculation only, not the 120001-node computation.
- The initial new Python script had an unterminated docstring and exited
  before producing an artifact. It was fixed and rerun; only the fixed
  successful run is used in the verdict.

Evidence: scripts/routea_derivative_ladder_2349.py,
scripts/routea_derivative_ladder_selftest_2349.py,
ConnesWeilRH/Dev/C1RouteABumpEnvelope.lean and paired Audit,
results/2349_derivative_ladder.json and paired validation JSON.
Logs: build-logs/2349_derivative_ladder_fixed.log,
build-logs/2349_selftest.log, build-logs/2349_regression.log,
build-logs/2349_bump_envelope_build.log.

## Next steps

1. Formalize the actual bump derivative recurrence through order four and
   instantiate the proved scalar envelope on the resulting polynomials.
   This replaces the remaining derivative-majorant hypothesis with a theorem;
   completion requires the real derivative of the same guarded owner,
   including both support edges, not merely the candidate jet expression.

2. Bind the ideal coefficients and import the finite directed node facts.
   This connects externally certified numbers to the function Lean actually
   consumes. Completion requires exact coefficient realization, evaluator
   semantics and node upper bounds, not matching hashes alone.

3. Return the completed norm supplier to the selected detector's signed
   physical-kernel budget at full composed support. This tests whether the
   improved bound removes a producer premise. Completion requires the same
   healthy owner and signed budget closure; it is not another unsigned norm
   improvement or a reopening of the frozen map-103 family.

