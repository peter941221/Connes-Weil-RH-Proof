# 085: Chebyshev Decoupling Route Architecture

**Status**: Active binding route record.
**Date**: 2026-09-22.
**Upstream**: `082`, `083`, `084`, Record 1836.
**Exit**: `ConnesWeilRH.Dev.C1P2DirectChebyshevDecoupling.riemannHypothesis_of_chebyshev_seminorm_bounds`.

---

## 1. Route Summary

The Chebyshev decoupling route realizes Option A (Direct Semi-Local Gate / Prime Absorption) by factoring the arithmetic prime-power sum into two mutually decoupled components:

1. **Arithmetic Mass Component**:
   ```text
   visibleChebyshevPrimeSum geometry = sum_{n in visible} Lambda(n)
   ```
   Purely number-theoretic, bounded asymptotically by $e^{2L}$ via Chebyshev's $\psi(x)$ theorem.

2. **Geometric / Analytic Profile Component**:
   ```text
   orbitChebyshevDecoupledBound geometry = 4 * L * exp(L) * S^2
   ```
   where $L = \text{orbitIndex} + 2$ and $S = \|\phi\|_\infty = \text{seminorm}(C, 0, 0, \phi)$.
   Purely functional-analytic, controlled by the unscaled orbit bump $\phi$.

3. **Master Majorant**:
   ```text
   finitePrimeSum(g * g) <= visibleChebyshevPrimeSum * (4 * L * exp(L) * S^2)
   ```

4. **Master Absorption Condition**:
   ```text
   visibleChebyshevPrimeSum * (4 * L * exp(L) * S^2) <= - archimedeanTerm(g * g)
   ```

## 2. Formal Exit Chain

```text
[Chebyshev Seminorm Majorant]
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

Each link in this chain is formally proved in Lean 4 without `sorryAx`, relying exclusively on standard axioms `[propext, Classical.choice, Quot.sound]`.
