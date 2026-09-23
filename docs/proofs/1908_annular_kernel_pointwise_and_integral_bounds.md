# 1908 — Annular Kernel Pointwise Domination, Total Integral Bounds, and Master Exit

Date: 2026-09-23.
Classification: FORMAL THEOREM (100% complete in Lean 4, standard axioms only).

## 1. Overview & Mathematical Architecture

In Record 1907 (`ConnesWeilRH.Dev.C1G8R3ConcreteWingMajorant`), the concrete annular wing majorant:
```lean
def concreteWingMajorant (N C : ℝ) (t : ℝ) : ℝ :=
  if N < |t| then C / t ^ 2 else 0
```
was formally constructed, and its individual wing integrals over $[N, \infty)$ and $(-\infty, -N]$
were bounded by $C / N$.

This record documents the complete formalization of the bridge connecting the operator-level
annular kernel diagonal to the concrete wing majorant across two new modules:
1. `ConnesWeilRH.Dev.C1G8R3ConcreteWingMajorantIntegral`:
   - Computes the total Lebesgue integral over the entire real line $\mathbb{R}$:
     $$\int_\mathbb{R} g(t) \, dt = \int_{-\infty}^{-N} g(t) \, dt + \int_{-N}^N g(t) \, dt + \int_N^\infty g(t) \, dt \le \frac{2C}{N}$$
   - Shows that any almost-everywhere pointwise bound by $g(t)$ integrates directly to $\le 2C/N$.
   - Deduces S3 survivor core square-summability from the total integral bound and from almost-everywhere pointwise domination.
   - Formalizes `riemannHypothesis_of_right_ae_pointwise_concrete_wing_majorant_and_aggregateEq`.

2. `ConnesWeilRH.Dev.C1G8R3AnnularKernelPointwiseBound`:
   - Proves the geometric property that the annular output window $Icc(-n, n) \setminus Icc(-N, N)$ is strictly contained in $\{t \in \mathbb{R} \mid N < |t|\}$.
   - Proves that the indicator enorm square commutes with summation.
   - Uses `ae_all_iff.mpr` to handle the countable family of almost-everywhere equalities relating `sourceRootAnnularOutputWindow` to the annular indicator of the unwindowed root convolution.
   - Directly deduces almost-everywhere pointwise domination by `concreteWingMajorant N C` from the unwindowed root convolution decay:
     $$\forall t, N < |t| \implies \sum_i \|(\mathcal{K}_{\text{root}} e_i)(t)\|_{\text{e}}^2 \le \frac{C}{t^2}$$
   - Formalizes `sourceCompressedRoot_squareSum_of_rootConvolution_decay` and the master exit `riemannHypothesis_of_right_rootConvolution_decay_and_aggregateEq` to Mathlib's `_root_.RiemannHypothesis`.

## 2. Core Theorems

### A. Total Integral Calculus (`C1G8R3ConcreteWingMajorantIntegral`)
- `lintegral_Ioo_concreteWingMajorant_eq_zero`:
  $$\int_{(-N, N)} g(t) \, dt = 0$$
- `lintegral_concreteWingMajorant_eq_wings`:
  $$\int_\mathbb{R} g(t) \, dt = \int_{(-\infty, -N]} g(t) \, dt + \int_{[N, \infty)} g(t) \, dt$$
- `lintegral_concreteWingMajorant_le`:
  $$\int_\mathbb{R} g(t) \, dt \le \frac{2C}{N}$$
- `lintegral_annular_output_le_of_ae_pointwise`:
  Integrating $\sum_i |(w_{N,n} e_i)(t)|^2 \le g(t)$ a.e. yields $\le 2C/N$.
- `sourceCompressedRoot_squareSum_of_ae_pointwise_concreteWingMajorant`:
  Discharges S3 survivor core summability from the a.e. pointwise bound.
- `riemannHypothesis_of_right_ae_pointwise_concrete_wing_majorant_and_aggregateEq`:
  Connects the a.e. pointwise bound directly to Mathlib RH.

### B. Pointwise Majorization & Root Convolution Decay (`C1G8R3AnnularKernelPointwiseBound`)
- `indicator_enorm_sq`:
  $$\|(s.1_A f)(x)\|^2 = s.1_A(\|f\|^2)(x)$$
- `mem_annulus_imp_abs_gt`:
  $$t \in [-n, n] \setminus [-N, N] \implies N < |t|$$
- `annulus_indicator_le_wing`:
  $$1_{[-n, n] \setminus [-N, N]}(t) \cdot v \le 1_{\{t \mid N < |t|\}}(t) \cdot v$$
- `sourceRootAnnularOutputWindow_tsum_le_concreteWingMajorant_of_root_decay`:
  Deduces the almost-everywhere pointwise majorization:
  $$\forall n \ge N, \forall^\text{m} t \, \partial\text{volume}, \sum_i \|(w_{N,n} e_i)(t)\|^2 \le g(t)$$
  from the unwindowed root convolution decay:
  $$\forall t, N < |t| \implies \sum_i \|(\mathcal{K}_{\text{root}} e_i)(t)\|^2 \le \frac{C}{t^2}$$
- `sourceCompressedRoot_squareSum_of_rootConvolution_decay`:
  Discharges S3 directly from the unwindowed root decay.
- `riemannHypothesis_of_right_rootConvolution_decay_and_aggregateEq`:
  Master exit to Mathlib RH from unwindowed root convolution decay and $\rho_5$ aggregate trace limit equality.

## 3. Axiom Audits & Verification

Both modules audited with zero `sorryAx` and standard foundation:
- `ConnesWeilRH.Dev.C1G8R3ConcreteWingMajorantIntegralAudit`:
  4081 jobs, 0 error lines, axioms: `[propext, Classical.choice, Quot.sound]`.
- `ConnesWeilRH.Dev.C1G8R3AnnularKernelPointwiseBoundAudit`:
  4082 jobs, 0 error lines, axioms: `[propext, Classical.choice, Quot.sound]`.
