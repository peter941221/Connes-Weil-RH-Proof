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

## 3. Producer-side reduction (record 1840)

The new theorem `exists_nat_geometric_budget_of_base_contraction` formally
reduces the orbit-index part of the budget obligation: if the selected base
satisfies `2 * seminorm(base) < 1`, then its geometric upper bound eventually
falls below every positive budget after multiplication by a fixed nonnegative
correction seminorm. This is a FORMAL conditional reduction, not a producer
existence theorem. The actual geometry constructor still has to realize the
chosen index and its interpolation, tail, square-zero, support, and
Archimedean-margin fields. The strict base contraction inequality remains
open for the constructor-selected owner.

## 4. Orbit-index quantifier boundary (record 1841)

The eventual-budget lemma is not yet directly consumable by the existing
geometry producer. `exists_orbitG8Geometry_of_sourceNontrivialZero_right`
constructs `OrbitG8Geometry rho g` with an existentially selected
`geometry.orbitIndex`; it does not accept a prescribed index from the caller.
Therefore the implication

```text
2 * seminorm(base) < 1
  -> choose a large index
  -> satisfy the harmonic budget
```

is not valid for the current owner without an additional theorem. The live
producer obligation is now one of:

1. strengthen the constructor to realize a caller-supplied orbit index while
   preserving interpolation, tail, square-zero, and margin fields; or
2. prove that a constructed owner can be lifted to larger orbit index with all
   those fields preserved.

This is a FORMAL quantifier/interface finding, not a no-go theorem and not an
RH result.
