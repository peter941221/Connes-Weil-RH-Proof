# 088: Convolution Seminorm Decay and Iterated Base Exit

**Status**: Active binding route record.
**Date**: 2026-09-22.
**Upstream**: `087`, Record 1839.
**Exit**: `ConnesWeilRH.Dev.C1P2ConvolutionSeminormBound.riemannHypothesis_of_iteratedBase_decay_and_harmonicBudget`.

---

## 1. Route Summary

This record completes the decoupling of the raw factor seminorm $S = \mathrm{seminorm}(\phi)$
by establishing exact L^1-to-L^\infty convolution contraction:

```text
rawFactorSeminorm geometry <=
  ||(convolutionIterate geometry.base geometry.orbitIndex).test.toLp 1|| *
    SchwartzMap.seminorm C 0 0 geometry.correction.test
```

and explicit geometric power contraction:

```text
rawFactorSeminorm geometry <=
  2 * ((2 * seminorm(base))^n * seminorm(base)) * seminorm(correction)
```

Connecting this contraction with the canonical harmonic budget:

```text
harmonicBudgetSeminorm geometry delta =
  sqrt(delta / (2 * exp(L) * (visibleHarmonicChebyshevSum + 1)))
```

produces the unified master exits:

```text
riemannHypothesis_of_iteratedBase_decay_and_harmonicBudget :
  (For each off-line zero rho, 1/2 < Re(rho), exists g, geometry, delta with:
     1. delta <= -archimedeanTerm g.convolutionSquare
     2. ||base^{*(n+1)}||_{L1} * seminorm(correction) <= harmonicBudgetSeminorm geometry delta)
  ==> _root_.RiemannHypothesis

riemannHypothesis_of_geometric_contraction_and_harmonicBudget :
  (For each off-line zero rho, 1/2 < Re(rho), exists g, geometry, delta with:
     1. delta <= -archimedeanTerm g.convolutionSquare
     2. 2 * ((2 * S_base)^n * S_base) * S_corr <= harmonicBudgetSeminorm geometry delta)
  ==> _root_.RiemannHypothesis
```

---

## 2. Structural Status of Option A

```text
+------------------------------------------------------------------------+
| Component                                            | Status          |
+------------------------------------------------------------------------+
| 1. Natural 2L Kernel Truncation                      | Formal (Closed) |
| 2. Pointwise cancellation (1/n inside prime sum)     | Formal (Closed) |
| 3. Harmonic Chebyshev Mertens reduction (2L)         | Formal (Closed) |
| 4. Unconditional prime sum dominance (all geom)     | Formal (Closed) |
| 5. Canonical harmonic budget spec (unconditional)    | Formal (Closed) |
| 6. L^1 to L^infty convolution seminorm contraction   | Formal (Closed) |
| 7. Geometric power decay bound (2*S_base)^n          | Formal (Closed) |
| 8. Iterated base decay master exit for RH            | Formal (Closed) |
| 9. Geometric contraction master exit for RH          | Formal (Closed) |
+------------------------------------------------------------------------+
```
