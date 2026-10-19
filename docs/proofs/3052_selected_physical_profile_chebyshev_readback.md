# Selected physical profile as a smoothed Chebyshev sum (record 3052)

Date: 2026-10-19.

Status: exact source-level algebraic reduction and analytic target. No new
Lean theorem, numerical certificate, selected-owner sign estimate, or RH proof.

## Owner and source expressions

Fix an actual `geometry : OrbitG8Geometry rho g`, and write
`phi = (orbitRawFactor geometry).test`. Its support is contained in
`(-L,L)`, where `L = geometry.orbitIndex + 2`. The selected owner test is the
half-density shift of `phi`, and its square's prime contribution is already
read back through `orbitPhysicalKernel` in
`C1P2OrbitPhysicalProfileReadback.lean`.

The source defines the common-factor profile as

```text
P(t) = sum over n in orbitVisiblePrimeRange geometry of
       2 * (Lambda(n) / sqrt(n)) * exp(log(n)/2 - t) * phi(log(n)-t).
```

Here `Lambda(n)` is the von Mangoldt weight: it is `log(p)` when `n` is a
power of a prime `p`, and zero otherwise. This is the arithmetic measure
whose smoothed sum appears in the explicit formula.

## Exact simplification

For every `n >= 2`, `exp(log(n)/2) = sqrt(n)`, so the square-root factors
cancel. The terms `n = 0` and `n = 1` vanish because their von Mangoldt
weights are zero. Therefore the profile has the exact form

```text
P(t) = 2 * exp(-t) * sum over n in orbitVisiblePrimeRange geometry of
       Lambda(n) * phi(log(n)-t).
```

This is an algebraic identity from the definitions, not an estimate. The
prime sum remains grouped before any absolute value is taken.

The real finite physical integrand is consequently

```text
F(t) = 2 * exp(-t) * Re(conj(phi(-t)) *
       sum over n in orbitVisiblePrimeRange geometry of
       Lambda(n) * phi(log(n)-t)).
```

The common raw factor is outside the whole arithmetic sum. Thus the exact
producer question is a signed correlation between the selected correction
`phi(-t)` and a smoothed Chebyshev prime-power profile. Taking norms term by
term would remove both prime cancellation inside the sum and phase
cancellation against `phi(-t)`.

## Connection to the discrepancy identity

For `g` the selected half-density test, define
`f(y) = Re(g.convolutionSquare.test y)` and
`H_g(y) = exp(-y/2) * f(y)`. The exact Stieltjes summation-by-parts identity
in proof record 1736 gives, on the same complete visible prime-power owner
and under the committed triple-vanishing condition,

```text
qw(g) = Q_cont(g) + 2 * integral_0^infinity R(y) * H_g'(y) dy,
R(y) = Psi(exp(y)) - (exp(y) - 1),
Psi(x) = sum over 2 <= n <= x of Lambda(n),
Q_cont(g) = 2 * integral_0^infinity exp(-y/2) * f(y) dy
            - archimedeanTerm(g.convolutionSquare).
```

The formula does not assume RH and does not discard the prime-power
discrepancy. It identifies the missing estimate: control the signed action of
the actual `R(y)` on `H_g'(y)` strongly enough to offset `Q_cont(g)` for the
selected geometry. Pointwise positivity is unavailable; record 1736 gives a
triple-vanishing test family for which the discrepancy integrand changes
sign. A density approximation that sets `R=0` also fails to supply the
required sign.

## Decision

The exact profile simplification removes a normalization distraction but does
not close the analytic gap. The next admissible Route-A result must either
prove the same-owner signed discrepancy inequality above, or derive an
equivalent signed node/integral certificate for
`orbitFinitePhysicalKernelIntegrand`. Record 3053 refines the continuous
component and gives the exact derivative-energy threshold the discrepancy
must overcome. The item-5 `chargeRest` enclosure and its repaired numerical
owner do not provide this estimate. No further item-5 cell batch or numerical
scan is justified until it removes a named premise of this selected-owner
target.

Evidence:

- `ConnesWeilRH/Dev/C1P2OrbitPhysicalProfileReadback.lean` defines the actual
  kernel and common-factor profile.
- `ConnesWeilRH/Dev/C1P2OrbitPhysicalKernelIntegrandBounds.lean` proves the
  profile factorization, real-integrand readback, support, and integral
  equalities.
- `docs/proofs/1736_detector_sign_translation_energy_and_prime_discrepancy.md`
  proves the paper-level energy and Stieltjes identities and records their
  scoped counterexamples to pointwise-sign and density-only shortcuts.
- `docs/proofs/3051_routea_corrected_next_gate.md` is superseded as to the
  item-5 evaluator being the binding selected-detector next gate.
