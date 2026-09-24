# 1947 — Vertex channel proof-contract audit

Date: 2026-09-24

## Audit result

The requested selected-owner conclusions are not derivable from the current
`HealthyYoshidaDetectorData` interface.

For the actual owner

```text
u = fullFunctionalEquationOrbitAnnihilator g rho
h(lambda) = u - lambda*g
lambda_v = B'/(2*C),
```

the existing formal layer supplies `C > 0`, the exact span parabola, and the
vertex identity. It does not supply any of the following:

1. an owner-specific upper/lower bound for `B'` or `C` sufficient to produce a
   useful explicit range for `lambda_v`;
2. an Archimedean signed estimate for the vertex quadratic;
3. a finite visible-prime signed estimate for the vertex quadratic.

`HealthyYoshidaDetectorData` contains smooth compact support, triple
vanishing, detection of `rho`, and positivity of the detector square's local
Weil sum. It contains no channel profile sign, moment bound, or prime-budget
field. Existing support lemmas prove only finiteness/range inclusion for the
visible-prime set. They do not control the signs of the four physical
profiles.

## Exact remaining contract

The next genuine analytic theorem must provide, for the actual selected owner,
some explicit `L >= 0` and `eta > 0` such that

```text
0 < lambda_v <= L
Q_arch(lambda_v) + Q_prime(lambda_v) <= -eta.
```

The stronger split target
`Q_arch(lambda_v) < 0` and `Q_prime(lambda_v) < 0` is supported by the
committed-class probe in record 1946, but is not implied by the present Lean
assumptions. A proof may instead establish the summed inequality while
retaining prime cancellation.

The parameter-range part is not independently blocking after such a theorem:
for fixed `rho` and an owner-specific finite `lambda_v`, the existing bounded-
coefficient tail theorem can take any explicitly supplied `L`. The real
missing premise is the signed channel estimate.

## Decision

Do not add a conditional Lean theorem that assumes the two channel signs.
Do not promote record 1946's committed-class numbers to the selected owner.
The next work must either construct a selected-owner shape/physical-kernel
certificate that supplies the contract above, or produce a reproducible
counterexample in the actual owner class.

Classification: interface/quantifier audit; no RH claim.
