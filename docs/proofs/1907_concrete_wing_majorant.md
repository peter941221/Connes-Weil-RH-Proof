# 1907 — Concrete Annular Wing Majorant and Master Exit to Mathlib RiemannHypothesis

Date: 2026-09-23.
Classification: FORMAL THEOREM (100% complete in Lean 4, standard axioms only).

## 1. Overview & Motivation

In Record 1733 (`sourceCompressedRoot_squareSum_of_annular_wing_majorant`) and Record 1906 (`C1G8MasterExit`),
the S3 survivor core square-summability obligation was reduced to exhibiting an annular wing majorant function
satisfying measurable integrability and compact support vanishing conditions.
In Records 1734 and 1735, the two-integration-by-parts argument and digamma vertical line bounds
established that the annular kernel diagonal satisfies an oscillatory decay rate of $O(t^{-2})$ outside $[-N, N]$.

This module (`ConnesWeilRH.Dev.C1G8R3ConcreteWingMajorant`) constructs the explicit concrete majorant:
```lean
def concreteWingMajorant (N C : ℝ) (t : ℝ) : ℝ :=
  if N < |t| then C / t ^ 2 else 0
```
and formally proves that it discharges every single structural premise required by the S3 master exit.

## 2. Formal Theorems

1. **Measurability and Symmetry**:
   - `concreteWingMajorant_measurable`: Borel measurable via `Measurable.piecewise`.
   - `concreteWingMajorant_nonneg`: Pointwise $0 \le g(t)$ for $0 \le C$.
   - `concreteWingMajorant_eq_zero_of_mem_Icc`: $g(t) = 0$ for $t \in [-N, N]$.
   - `concreteWingMajorant_neg`: Even function $g(-t) = g(t)$.

2. **Decay and Integral Bounds**:
   - `concreteWingMajorant_le_rpow_neg_two`: $g(t) \le C \cdot t^{-2}$ on $[N, \infty)$.
   - `real_integral_Ici_const_rpow_neg_two`:
     $$\int_N^\infty \frac{C}{t^2} dt = \frac{C}{N}$$
     verified via `integral_Ioi_rpow_of_lt` with exponent $-2 < -1$.
   - `lintegral_Ici_concreteWingMajorant_le`:
     $$\int_N^\infty g(t) dt \le \frac{C}{N}$$
     in `ENNReal` via Lebesgue dominated integral comparison (`setLIntegral_le_of_le_nnreal`).
   - `lintegral_Iic_concreteWingMajorant_le`:
     $$\int_{-\infty}^{-N} g(t) dt \le \frac{C}{N}$$
     in `ENNReal` via measure-preserving negation reflection `Measure.measurePreserving_neg`.

3. **Discharge of S3 Structural Hypotheses**:
   - `sourceCompressedRoot_squareSum_of_concreteWingMajorant`:
     Discharges all 5 abstract hypotheses of `sourceCompressedRoot_squareSum_of_annular_wing_majorant`,
     reducing S3 solely to the pointwise bound:
     $$\sum_i |(w_{N,n} e_i)(t)|^2 \le g(t)$$

4. **Master Exit to Mathlib `_root_.RiemannHypothesis`**:
   - `riemannHypothesis_of_right_concrete_wing_majorant_and_aggregateEq`:
     Connects the concrete wing majorant directly to Mathlib RH.

## 3. Axioms and Verification

Verified in `ConnesWeilRH.Dev.C1G8R3ConcreteWingMajorantAudit`:
- Focused build log: `build-logs/1907_concrete_wing_majorant.log`
- Jobs: 4080
- Errors: 0
- Warnings: 0 (in module)
- `sorryAx`: 0
- Axioms: `[propext, Classical.choice, Quot.sound]`
