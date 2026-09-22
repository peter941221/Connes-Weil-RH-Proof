# 086: Chebyshev Sharpened Integral Decoupling Route

**Status**: Active binding route record.
**Date**: 2026-09-22.
**Upstream**: `085`, Record 1837.
**Exit**: `ConnesWeilRH.Dev.C1P2DirectChebyshevSharpenedDecoupling.riemannHypothesis_of_chebyshev_sharpened_bounds`.

---

## 1. Route Summary

The sharpened Chebyshev decoupling route sharpens Option A (Chebyshev Decoupling, `085`) by replacing the uniform dilation supremum with the exact reflected exponential integral:

1. **Exact Integral Kernel**:
   ```text
   integral_{-L}^L exp(-t) dt = exp(L) - exp(-L) = 2 * sinh(L)
   ```

2. **Sharpened Decoupled Bound**:
   ```text
   orbitChebyshevSharpenedBound geometry = 2 * (exp(L) - exp(-L)) * S^2
   ```
   where $L = \text{orbitIndex} + 2$ and $S = \|\phi\|_\infty$. This eliminates the polynomial $2L$ penalty from `085`.

3. **Master Sharpened Majorant**:
   ```text
   finitePrimeSum(g * g) <= visibleChebyshevPrimeSum * (2 * (exp(L) - exp(-L)) * S^2)
   ```

4. **Master Sharpened Absorption Condition**:
   ```text
   visibleChebyshevPrimeSum * (2 * (exp(L) - exp(-L)) * S^2) <= - archimedeanTerm(g * g)
   ```

## 2. Formal Exit Chain

```text
[Sharpened Chebyshev Bound]
           |
           v
[OrbitG8AbsorptionWitness rho]
           |
           v
[SourceRH]
           |
           v
[RiemannHypothesis] (_root_.RiemannHypothesis)
```

Verified in Lean 4 with standard axioms only: `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.
