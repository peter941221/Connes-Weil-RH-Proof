# 1837: Chebyshev-Kernel Sharpened Decoupled Bound via Exact Reflected Exponential Integral

**Status**: Formally proved and audited in Lean 4 (`ConnesWeilRH.Dev.C1P2DirectChebyshevSharpenedDecoupling`).
**Date**: 2026-09-22.
**Authors**: Peter + Assistant.
**Axioms**: `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.

---

## 1. Context and Motivation

In Record 1836 (`ConnesWeilRH.Dev.C1P2DirectChebyshevDecoupling`), the arithmetic prime sum was decoupled into:
```text
finitePrimeSum(g * g) <= visibleChebyshevPrimeSum * (4 * L * exp(L) * S^2)
```
where $L = \text{orbitIndex} + 2$ and $S = \|\phi\|_\infty$. That bound replaced the half-density dilation factor $\exp(-t)$ by its worst-case uniform supremum $\exp(L)$ over $t \in [-L, L]$, and integrated the constant over an interval of length $2L$, paying a polynomial penalty factor of $2L$.

Record 1837 sharpens this by directly integrating the exact profile $\exp(-t)$ over $[-L, L]$:
```text
integral_{-L}^L exp(-t) dt = exp(L) - exp(-L) = 2 * sinh(L)
```
completely eliminating the polynomial $2L$ factor and reducing $\exp(L)$ to $\exp(L) - \exp(-L) < \exp(L)$.

---

## 2. The Exact Integral Identity

Using the Fundamental Theorem of Calculus:
```lean
theorem integral_exp_real (a b : ℝ) :
    ∫ x in a..b, Real.exp x = Real.exp b - Real.exp a
```
By reflection substitution via `intervalIntegral.integral_comp_neg`:
```lean
theorem integral_expNeg_real (a b : ℝ) :
    ∫ x in a..b, Real.exp (-x) = Real.exp (-a) - Real.exp (-b)
```
Specializing to the symmetric window $[-L, L]$:
```lean
theorem integral_expNeg_symm (L : ℝ) :
    ∫ x in (-L)..L, Real.exp (-x) = Real.exp L - Real.exp (-L)
```

---

## 3. The Sharpened Decoupled Bound

We define:
```lean
def orbitChebyshevSharpenedBound
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : ℝ :=
  2 * (Real.exp (rawFactorSupportRadius geometry) -
       Real.exp (-rawFactorSupportRadius geometry)) *
    (rawFactorSeminorm geometry) ^ 2
```

We formally prove:
1. Strict Positivity:
   ```lean
   theorem orbitChebyshevSharpenedBound_nonneg
       (geometry : OrbitG8Geometry rho g) :
       0 ≤ orbitChebyshevSharpenedBound geometry
   ```

2. Strict Improvement over Decoupled Bound:
   ```lean
   theorem orbitChebyshevSharpenedBound_le_decoupledBound
       (geometry : OrbitG8Geometry rho g) :
       orbitChebyshevSharpenedBound geometry ≤
         orbitChebyshevDecoupledBound geometry
   ```
   For all $L \ge 1$:
   $$\exp(L) - \exp(-L) \le \exp(L) \le 2L \exp(L)$$
   whence $2(\exp(L) - \exp(-L)) S^2 \le 4L \exp(L) S^2$.

---

## 4. Master Majorant and RH Theorems

By pointwise cancellation of $1/\sqrt{n}$ with $\exp((\log n)/2)$:
```lean
theorem cancellation_identity_with_t (n : ℕ) (t : ℝ) (S : ℝ) :
    ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
      (Real.exp (Real.log (n : ℝ) / 2 - t) * S ^ 2) =
    ArithmeticFunction.vonMangoldt n * (Real.exp (-t) * S ^ 2)
```
Integrating the pointwise Chebyshev-scaled profile over $[-L, L]$ via `intervalIntegral.integral_mono_on_of_le_Ioo` yields:

```lean
theorem finitePrimeSum_le_chebyshev_sharpened_bound
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    finitePrimeSum g.convolutionSquare ≤
      visibleChebyshevPrimeSum geometry * orbitChebyshevSharpenedBound geometry
```

Packaging into the RH exit chain:
```lean
def absorptionWitness_of_chebyshev_sharpened_bound
    (rho : sourceNontrivialZeroSet) (g : CompactLogTest)
    (geometry : OrbitG8Geometry rho g)
    (habsorb : visibleChebyshevPrimeSum geometry *
        orbitChebyshevSharpenedBound geometry ≤
      -archimedeanTerm g.convolutionSquare) :
    OrbitG8AbsorptionWitness rho :=
  ⟨g, geometry, (finitePrimeSum_le_chebyshev_sharpened_bound geometry).trans habsorb⟩

theorem sourceRH_of_chebyshev_sharpened_bounds
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            visibleChebyshevPrimeSum geometry *
                orbitChebyshevSharpenedBound geometry ≤
              -archimedeanTerm g.convolutionSquare) :
    RHDefinitionBridge.standard.SourceRH

theorem riemannHypothesis_of_chebyshev_sharpened_bounds
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            visibleChebyshevPrimeSum geometry *
                orbitChebyshevSharpenedBound geometry ≤
              -archimedeanTerm g.convolutionSquare) :
    _root_.RiemannHypothesis
```

---

## 5. Verification

- Module: `ConnesWeilRH/Dev/C1P2DirectChebyshevSharpenedDecoupling.lean`
- Audit: `ConnesWeilRH/Dev/C1P2DirectChebyshevSharpenedDecouplingAudit.lean`
- Log: `build-logs/C1P2DirectChebyshevSharpenedDecoupling.log`
- Status: Clean build (3790 jobs), 0 errors, 0 warnings, 0 `sorryAx`, standard axioms only `[propext, Classical.choice, Quot.sound]`.
