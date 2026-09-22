# 1839: Convolution L-infinity Seminorm Decay and Iterated Base Exit

**Status**: Formally verified in Lean 4.
**Date**: 2026-09-22.
**Module**: `ConnesWeilRH.Dev.C1P2ConvolutionSeminormBound`, `ConnesWeilRH.Dev.C1P2ConvolutionSeminormBoundAudit`.
**Axioms**: `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.
**Build**: 3900 jobs clean.

---

## 1. Mathematical Summary

This record proves the fundamental L-infinity (order 0-0 Schwartz seminorm)
contraction theorem for convolutions of compactly supported test functions on R:

```text
seminorm(f * g) <= ||f||_{L1} * seminorm(g)
                <= (c - a) * seminorm(f) * seminorm(g)
```

where `Function.support f.test ⊆ Set.Icc a c`.

Applied to the iterated base `base^{*(n+1)}` on `[-1, 1]` with support length `2`:

```text
seminorm(base^{*n}) <= ((c - a) * seminorm(base))^n * seminorm(base)
```

Applied to the selected healthy-owner unscaled orbit factor
`orbitRawFactor geometry = (convolutionIterate base n).convolution correction`:

```text
rawFactorSeminorm geometry <=
  ||(convolutionIterate geometry.base geometry.orbitIndex).test.toLp 1|| *
    SchwartzMap.seminorm C 0 0 geometry.correction.test

rawFactorSeminorm geometry <=
  2 * ((2 * seminorm(base))^n * seminorm(base)) * seminorm(correction)
```

Connecting this bound with the canonical harmonic budget seminorm threshold
`harmonicBudgetSeminorm geometry delta` from Record 1838 yields the master exit
theorems:
- `sourceRH_of_iteratedBase_decay_and_harmonicBudget`
- `riemannHypothesis_of_iteratedBase_decay_and_harmonicBudget`
- `sourceRH_of_geometric_contraction_and_harmonicBudget`
- `riemannHypothesis_of_geometric_contraction_and_harmonicBudget`

---

## 2. Core Declarations

```text
+------------------------------------------------------------------------+
| Declaration                                            | Status        |
+------------------------------------------------------------------------+
| norm_convolution_integrand_le_seminorm                 | Formal Lean 4 |
| integrable_convolution_integrand                       | Formal Lean 4 |
| norm_convolution_apply_le_seminorm                     | Formal Lean 4 |
| seminorm_convolution_le_integral_mul_seminorm          | Formal Lean 4 |
| seminorm_convolution_le_toLp_one_mul_seminorm          | Formal Lean 4 |
| seminorm_convolution_le_supportLength_mul_seminorm     | Formal Lean 4 |
| convolution_apply_comm                                 | Formal Lean 4 |
| seminorm_convolution_comm                              | Formal Lean 4 |
| seminorm_convolution_le_supportLength_mul_seminorm_right | Formal Lean 4 |
| seminorm_convolutionIterate_le_pow                     | Formal Lean 4 |
| rawFactorSeminorm_le_toLp_one_mul_seminorm             | Formal Lean 4 |
| rawFactorSeminorm_le_geometric_bound                   | Formal Lean 4 |
| sourceRH_of_iteratedBase_decay_and_harmonicBudget      | Formal Lean 4 |
| riemannHypothesis_of_iteratedBase_decay_and_harmonicBudget | Formal Lean 4 |
| sourceRH_of_geometric_contraction_and_harmonicBudget   | Formal Lean 4 |
| riemannHypothesis_of_geometric_contraction_and_harmonicBudget | Formal Lean 4 |
+------------------------------------------------------------------------+
```

---

## 3. Proof Mechanics

1. **Integrand Pointwise Bound**:
   For any Schwartz functions `f` and `g`, and any `x, t in R`:
   ```text
   ||f(t) * g(x - t)|| = ||f(t)|| * ||g(x - t)||
                       <= ||f(t)|| * seminorm(g)
   ```
   via `SchwartzMap.norm_le_seminorm C g.test (x - t)`.

2. **Integrability**:
   `fun t => f.test t * g.test (x - t)` is strongly measurable by continuity,
   and dominated by `fun t => ||f.test t|| * seminorm(g)`. Since `f` is Schwartz,
   its norm is integrable. By `Integrable.mono'`, the integrand is integrable.

3. **Integral Domination**:
   ```text
   ||(f * g)(x)|| = ||integral t, f(t) * g(x - t) dt||
                  <= integral t, ||f(t) * g(x - t)|| dt
                  <= integral t, ||f(t)|| * seminorm(g) dt
                  = (integral t, ||f(t)|| dt) * seminorm(g)
   ```
   evaluated cleanly via `integral_mul_const`.

4. **Seminorm Passage**:
   Taking the supremum over all `x in R` via `SchwartzMap.seminorm_le_bound C 0 0`:
   ```text
   seminorm(f * g) <= ||f||_{L1} * seminorm(g)
   ```

5. **Compact Support Factoring**:
   Using `norm_toLp_one_le_supportLength_mul_seminorm` from `CCM24FiniteSRootConvolutionNorm`:
   ```text
   seminorm(f * g) <= (c - a) * seminorm(f) * seminorm(g)
   ```

6. **Grand Master Exit**:
   Directly feeds `riemannHypothesis_of_harmonicBudgetSeminorm`, proving that
   bounding the L1 norm of `base^{*(n+1)}` below the canonical budget ensures
   Mathlib canonical `_root_.RiemannHypothesis`.
