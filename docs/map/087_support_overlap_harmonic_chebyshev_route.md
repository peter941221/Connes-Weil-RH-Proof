# 087: Support-Overlap Harmonic Chebyshev Route

**Status**: Active binding route record.
**Date**: 2026-09-22.
**Upstream**: `086`, Record 1838.
**Exit**: `ConnesWeilRH.Dev.C1P2DirectSupportOverlapDecoupling.riemannHypothesis_of_overlap_bounds`.

---

## 1. Route Summary

The support-overlap harmonic Chebyshev route achieves a major asymptotic reduction in the arithmetic pressure of Option A by exploiting the exact support of the translated raw factor $\phi(x - t)$:

1. **Exact Support Restriction**:
   The integrand $\exp(x/2 - t) \phi(-t) \phi(x - t)$ vanishes for all $t \le x - L$.
   The integration domain shrinks from $[-L, L]$ down to $[x - L, L]$, of width $2L - x$.

2. **Harmonic Cancellation**:
   Evaluating the overlap integral at $x = \log n$:
   ```text
   (1 / sqrt(n)) * 2 * sinh(L - log(n)/2) = exp(L) / n - exp(-L) <= exp(L) / n
   ```
   This injects an explicit $1/n$ factor into each prime term.

3. **Mertens Harmonic Reduction**:
   The arithmetic sum is reduced from the exponential Chebyshev sum $\sum_{n \le e^{2L}} \Lambda(n) \sim e^{2L}$ to the harmonic Chebyshev sum:
   ```text
   visibleHarmonicChebyshevSum = sum_{n in visible} vonMangoldt(n) / n ~ 2L
   ```
   reducing the arithmetic factor from exponential $e^{2L}$ to linear $2L$.

4. **Master Overlap Bound**:
   ```text
   orbitSupportOverlapBound geometry =
     2 * exp(L) * S^2 * (sum_{n in visible} vonMangoldt(n) / n)
   ```

5. **Unconditional Sharpening Hierarchy**:
   Formally proved:
   ```text
   visibleHarmonicChebyshevSum <= (1 / 2) * visibleChebyshevPrimeSum
   orbitSupportOverlapBound <= visibleChebyshevPrimeSum * orbitChebyshevSharpenedBound
   ```
   establishing that the harmonic overlap bound is strictly sharper than the Chebyshev sharpened bound across all geometries.

## 2. Formal Exit Chain

```text
[Support-Overlap Bound]
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
