# 1836: Chebyshev-Kernel Pointwise Cancellation and Seminorm-Decoupled Bound

**Status**: Formally proved and audited in Lean 4 (`ConnesWeilRH.Dev.C1P2DirectChebyshevDecoupling`).
**Date**: 2026-09-22.
**Authors**: Peter + Assistant.
**Axioms**: `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.

---

## 1. Context and Motivation

In the Option A semi-local gate assault (`082`, `083`, `084`), the goal is to establish:
```text
finitePrimeSum g.convolutionSquare <= - archimedeanTerm g.convolutionSquare
```
for an orbit-supported detector `g` with geometry `OrbitG8Geometry rho g`.

Previous records (`084`, Record 1835) established the factored profile majorant:
```text
finitePrimeSum g.convolutionSquare <= visiblePrimeWeightSum geometry * B
```
and bounded this by `visibleChebyshevPrimeSum geometry * B`.

However, the question remained: what is the concrete analytic structure of `B`? Does `B` grow with the primes `n`, or is it completely uniform?

## 2. The Fundamental Cancellation Identity

The term in the Weil explicit formula at prime-power $n$ is:
```text
(vonMangoldt n / sqrt(n)) * (F(log n) + F(-log n))
```
On a genuine convolution square $F = g \star g$, the bilateral profile is:
```text
F(log n) + F(-log n) = 2 * Re(g.convolutionSquare(log n))
```
Expressing this in terms of the raw unscaled factor $\phi = (\text{orbitRawFactor}\ \text{geometry}).test$:
```text
g.convolutionSquare(x) = integral_{-L}^L orbitWeightedKernelIntegrand geometry x t dt
```
where $L = \text{orbitIndex} + 2$ and:
```text
orbitWeightedKernelIntegrand geometry x t =
  exp(x / 2 - t) * star(phi(-t)) * phi(x - t)
```
Evaluating at $x = \log n$:
```text
exp(log(n) / 2 - t) = exp(log(n) / 2) * exp(-t) = sqrt(n) * exp(-t)
```
Therefore:
```text
(1 / sqrt(n)) * exp(log(n) / 2 - t) = (1 / sqrt(n)) * sqrt(n) * exp(-t) = exp(-t)
```
The arithmetic factor $1/\sqrt{n}$ from the Weil explicit formula cancels the half-density dilation factor $\exp((\log n)/2) = \sqrt{n}$ pointwise and identically for every $n \ge 1$. For $n = 0$, both sides vanish because $\Lambda(0) = 0$.

Formally proved in Lean as:
```lean
theorem cancellation_identity (n : ℕ) (L : ℝ) (S : ℝ) :
    ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
      (Real.exp (Real.log (n : ℝ) / 2 + L) * S ^ 2) =
    ArithmeticFunction.vonMangoldt n * (Real.exp L * S ^ 2)
```

## 3. The Seminorm-Decoupled Bound

Bounding the raw test functions by their $L^\infty$ Schwartz seminorm:
```text
S = SchwartzMap.seminorm C 0 0 phi
```
we have:
```text
||star(phi(-t)) * phi(log n - t)|| <= S^2
```
Since $t \in (-L, L)$, we have $-t < L$, so $\exp(-t) \le \exp(L)$.
Thus the pointwise integrand bound is:
```text
2 * (vonMangoldt n / sqrt(n)) * (exp(log n / 2 + L) * S^2)
  = vonMangoldt n * (2 * exp(L) * S^2)
```
Summing over all visible prime powers $n \in \text{orbitVisiblePrimeRange}$:
```text
sum_n vonMangoldt n * (2 * exp(L) * S^2)
  = visibleChebyshevPrimeSum geometry * (2 * exp(L) * S^2)
```
Integrating over $t \in (-L, L)$, which has interval length $2L$:
```text
intervalIntegral_{-L}^L dt [ visibleChebyshevPrimeSum * (2 * exp(L) * S^2) ]
  = visibleChebyshevPrimeSum geometry * (4 * L * exp(L) * S^2)
```

We define:
```lean
def orbitChebyshevDecoupledBound (geometry : OrbitG8Geometry rho g) : ℝ :=
  4 * rawFactorSupportRadius geometry *
    Real.exp (rawFactorSupportRadius geometry) *
    (rawFactorSeminorm geometry) ^ 2
```

## 4. Master Bounds and RH Implications

1. Direct Majorant:
```lean
theorem finitePrimeSum_le_chebyshev_seminorm_bound
    (geometry : OrbitG8Geometry rho g) :
    finitePrimeSum g.convolutionSquare <=
      visibleChebyshevPrimeSum geometry * orbitChebyshevDecoupledBound geometry
```

2. Direct Absorption Witness Constructor:
```lean
def absorptionWitness_of_chebyshev_seminorm_bound
    (rho : sourceNontrivialZeroSet) (g : CompactLogTest)
    (geometry : OrbitG8Geometry rho g)
    (habsorb : visibleChebyshevPrimeSum geometry *
        orbitChebyshevDecoupledBound geometry <=
      -archimedeanTerm g.convolutionSquare) :
    OrbitG8AbsorptionWitness rho
```

3. Exit to Mathlib Riemann Hypothesis:
```lean
theorem riemannHypothesis_of_chebyshev_seminorm_bounds
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            visibleChebyshevPrimeSum geometry *
                orbitChebyshevDecoupledBound geometry ≤
              -archimedeanTerm g.convolutionSquare) :
    _root_.RiemannHypothesis
```

## 5. Significance

This completely closes the decoupling of the arithmetic prime sum from the detector's analytic profile:
- Arithmetic mass is encapsulated in `visibleChebyshevPrimeSum geometry` ($\sum_{n \le e^{2L}} \Lambda(n) \sim e^{2L}$).
- Geometric profile is encapsulated in `orbitChebyshevDecoupledBound geometry` ($4 L e^L S^2$).
- Absorption requires only that the negative Archimedean margin exceeds this product.
