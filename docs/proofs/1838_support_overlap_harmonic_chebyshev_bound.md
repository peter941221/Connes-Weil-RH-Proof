# 1838: Support-Overlap Decoupling and Harmonic Chebyshev Bound

**Status**: Formally proved and audited in Lean 4 (`ConnesWeilRH.Dev.C1P2DirectSupportOverlapDecoupling`).
**Date**: 2026-09-22.
**Authors**: Peter + Assistant.
**Axioms**: `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.

---

## 1. Context and Motivation

In Records 1836 (`085`) and 1837 (`086`), the arithmetic prime sum was decoupled using the full symmetric window $[-L, L]$ of width $2L$. While 1837 eliminated the polynomial $2L$ factor via exact integration, the arithmetic factor remained the unweighted Chebyshev sum:
```text
visibleChebyshevPrimeSum = sum_{n in visible} vonMangoldt(n) ~ exp(2L)
```
which exhibits exponential growth in $L$.

Record 1838 discovers and formalizes the exact support restriction of the two-point integrand:
```text
orbitWeightedKernelIntegrand geometry x t = exp(x/2 - t) * star(phi(-t)) * phi(x - t)
```
Since $\text{supp}(\phi) \subseteq (-L, L)$, the factor $\phi(x - t)$ vanishes whenever $x - t \ge L$, which is $t \le x - L$. Therefore, the integration domain shrinks from $[-L, L]$ down to $[x - L, L]$, of width $2L - x$.

Evaluating this integral at $x = \log n$ produces an explicit factor of $1/n$ inside the arithmetic sum:
```text
(1 / sqrt(n)) * 2 * sinh(L - log(n)/2) = exp(L) / n - exp(-L)
```
which transforms the arithmetic sum from the exponential Chebyshev sum $\sum \Lambda(n) \sim e^{2L}$ into the harmonic Chebyshev sum:
```text
sum_{n in visible} vonMangoldt(n) / n ~ 2L
```
reducing the arithmetic growth from exponential $e^{2L}$ to linear $2L$ (a reduction by a factor of $e^{2L} / (2L)$).

---

## 2. The Overlap Vanishing Theorem

```lean
theorem orbitWeightedKernelIntegrand_eq_zero_of_lt_sub
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (x t : ℝ)
    (ht : t ≤ x - rawFactorSupportRadius geometry) :
    orbitWeightedKernelIntegrand geometry x t = 0
```
For $t \le x - L$, $x - t \ge L$, so $x - t \notin (-L, L)$ and $\phi(x - t) = 0$.

Furthermore, summing over all visible primes $n \ge 2$ yields uniform vanishing on the left interval:
```lean
theorem orbitFinitePhysicalKernelIntegrand_eq_zero_of_lt_log2_sub
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (t : ℝ)
    (ht : t ≤ Real.log 2 - rawFactorSupportRadius geometry) :
    orbitFinitePhysicalKernelIntegrand geometry t = 0

theorem integral_orbitFinitePhysicalKernelIntegrand_eq_log2_sub_interval
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    (∫ t in (-rawFactorSupportRadius geometry)..
        (rawFactorSupportRadius geometry),
        orbitFinitePhysicalKernelIntegrand geometry t) =
      ∫ t in (Real.log 2 - rawFactorSupportRadius geometry)..
        (rawFactorSupportRadius geometry),
        orbitFinitePhysicalKernelIntegrand geometry t
```
The integration domain shrinks from $[-L, L]$ (length $2L$) to $[\log 2 - L, L]$ (length $2L - \log 2$).

---

## 3. The Scaled Overlap Integral

```lean
theorem integral_scaled_expNeg_overlap (L x : ℝ) :
    ∫ t in (x - L)..L, Real.exp (x / 2 - t) =
      Real.exp (L - x / 2) - Real.exp (-(L - x / 2))
```

---

## 4. The Harmonic Cancellation Identity

```lean
theorem cancellation_identity_overlap (n : ℕ) (L : ℝ) (S : ℝ) :
    ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
      ((Real.exp (L - Real.log (n : ℝ) / 2) -
        Real.exp (-(L - Real.log (n : ℝ) / 2))) * S ^ 2) =
    ArithmeticFunction.vonMangoldt n *
      ((Real.exp L / (n : ℝ) - Real.exp (-L)) * S ^ 2)
```

---

## 5. Master Definitions and RH Theorems

We define:
```lean
def visibleHarmonicChebyshevSum
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : ℝ :=
  ∑ n ∈ orbitVisiblePrimeRange geometry,
    ArithmeticFunction.vonMangoldt n / (n : ℝ)

def orbitSupportOverlapBound
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : ℝ :=
  2 * Real.exp (rawFactorSupportRadius geometry) *
    (rawFactorSeminorm geometry) ^ 2 *
    visibleHarmonicChebyshevSum geometry
```

We establish the unconditional sharpening hierarchy:
```lean
theorem visibleHarmonicChebyshevSum_le_half_chebyshev
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    visibleHarmonicChebyshevSum geometry ≤
      (1 / 2 : ℝ) * visibleChebyshevPrimeSum geometry

theorem orbitSupportOverlapBound_le_chebyshev_sharpened_bound
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    orbitSupportOverlapBound geometry ≤
      visibleChebyshevPrimeSum geometry * orbitChebyshevSharpenedBound geometry
```

And formally prove:
```lean
theorem sourceRH_of_overlap_bounds
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            orbitSupportOverlapBound geometry ≤
              -archimedeanTerm g.convolutionSquare ∧
            finitePrimeSum g.convolutionSquare ≤
              orbitSupportOverlapBound geometry) :
    RHDefinitionBridge.standard.SourceRH

theorem riemannHypothesis_of_overlap_bounds
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            orbitSupportOverlapBound geometry ≤
              -archimedeanTerm g.convolutionSquare ∧
            finitePrimeSum g.convolutionSquare ≤
              orbitSupportOverlapBound geometry) :
    _root_.RiemannHypothesis
```

---

## 6. Natural 2L Kernel Truncation

Since $\text{supp}(\phi) \subseteq (-L, L)$, for any prime power $n$ with $\log n \ge 2L$, the integration interval $[x - L, L] = [\log n - L, L]$ is empty because $\log n - L \ge 2L - L = L$. Thus the integrand vanishes identically everywhere on $\mathbb{R}$:

```lean
theorem orbitWeightedKernelIntegrand_eq_zero_of_ge_two_L
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (n : ℕ) (t : ℝ)
    (hn : 2 * rawFactorSupportRadius geometry ≤ Real.log (n : ℝ)) :
    orbitWeightedKernelIntegrand geometry (Real.log (n : ℝ)) t = 0

theorem orbitPhysicalKernel_eq_zero_of_ge_two_L
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (n : ℕ)
    (hn : 2 * rawFactorSupportRadius geometry ≤ Real.log (n : ℝ)) :
    orbitPhysicalKernel geometry (Real.log (n : ℝ)) = 0
```

This establishes that all prime powers $n \ge \exp(2L)$ contribute identically zero to the physical kernel, naturally truncating the infinite Weil arithmetic sum to the finite range $\log n < 2L$.

---

## 7. Unconditional Arithmetic Dominance Discharged

By decomposing the physical kernel into node bounds on each prime power $n$, we formally establish that the arithmetic prime sum is unconditionally bounded by the support-overlap bound across all geometries:

```lean
theorem finitePrimeSum_le_orbitSupportOverlapBound
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    finitePrimeSum g.convolutionSquare ≤ orbitSupportOverlapBound geometry

theorem sourceRH_of_supportOverlapAbsorption
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            orbitSupportOverlapBound geometry ≤
              -archimedeanTerm g.convolutionSquare) :
    RHDefinitionBridge.standard.SourceRH

theorem riemannHypothesis_of_supportOverlapAbsorption
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            orbitSupportOverlapBound geometry ≤
              -archimedeanTerm g.convolutionSquare) :
    _root_.RiemannHypothesis
```

This completely eliminates the arithmetic prime sum conjunct from the RH hypothesis, reducing the entire RH proof to single Archimedean positivity absorption:
$$\text{orbitSupportOverlapBound geometry} \le -\text{archimedeanTerm}(g \ast g)$$

---

## 8. Verification

- Module: `ConnesWeilRH/Dev/C1P2DirectSupportOverlapDecoupling.lean`
- Audit: `ConnesWeilRH/Dev/C1P2DirectSupportOverlapDecouplingAudit.lean`
- Log: `build-logs/C1P2DirectSupportOverlapDecoupling.log`
- Status: Clean build (3791 jobs), 0 errors, 0 warnings, 0 `sorryAx`, standard axioms only `[propext, Classical.choice, Quot.sound]`.
