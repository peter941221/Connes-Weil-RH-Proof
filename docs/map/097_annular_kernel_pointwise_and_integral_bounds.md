# 097 — Annular Kernel Pointwise Domination, Total Integral Bounds, and Master Exit

Date: 2026-09-23.
Status: FORMAL THEOREM COMPLETE (Lean 4 / standard axioms only).

## 1. Context & Placement

Building on Map 096 (`concreteWingMajorant`), this map records the completion of the
bridge between the operator-level annular kernel diagonal and the concrete wing majorant
$g(t) = \text{if } N < |t| \text{ then } C / t^2 \text{ else } 0$:

1. **Total Integral Calculus** (`ConnesWeilRH.Dev.C1G8R3ConcreteWingMajorantIntegral`):
   Formalizes the full-line Lebesgue integral $\int_\mathbb{R} g(t) \, dt \le 2C / N$
   by decomposing $\mathbb{R} = (-\infty, -N] \cup (-N, N) \cup [N, \infty)$ and using
   the vanishing of $g$ on $[-N, N]$. Shows that any almost-everywhere pointwise majorant
   integrates to $\le 2C/N$, completely discharging S3 survivor core square-summability.

2. **Pointwise Annular Domination from Root Decay** (`ConnesWeilRH.Dev.C1G8R3AnnularKernelPointwiseBound`):
   Proves that the annular output window $Icc(-n, n) \setminus Icc(-N, N)$ is contained in
   $\{t \mid N < |t|\}$, and uses countable almost-everywhere interchange (`ae_all_iff.mpr`)
   to prove that the annular kernel diagonal sum is almost everywhere dominated by $g(t)$
   whenever the unwindowed root convolution column energy decays as $C / t^2$.

3. **Master Exit to Mathlib RiemannHypothesis**:
   `riemannHypothesis_of_right_rootConvolution_decay_and_aggregateEq` proves Mathlib's
   canonical `_root_.RiemannHypothesis` directly from:
   - detector data against hypothetical off-line zeros;
   - unwindowed root convolution decay: $\sum_i \|(\mathcal{K}_{\text{root}} e_i)(t)\|^2 \le C / t^2$ for $|t| > N$;
   - $\rho_5$ aggregate endpoint trace limit equality.

## 2. Core Lean Declarations

In `ConnesWeilRH.Dev.C1G8R3ConcreteWingMajorantIntegral`:
- `lintegral_Ioo_concreteWingMajorant_eq_zero`
- `lintegral_concreteWingMajorant_eq_wings`
- `lintegral_concreteWingMajorant_le`
- `sourceCompressedRoot_squareSum_of_lintegral_concreteWingMajorant`
- `lintegral_annular_output_le_of_ae_pointwise`
- `sourceCompressedRoot_squareSum_of_ae_pointwise_concreteWingMajorant`
- `riemannHypothesis_of_right_ae_pointwise_concrete_wing_majorant_and_aggregateEq`

In `ConnesWeilRH.Dev.C1G8R3AnnularKernelPointwiseBound`:
- `indicator_enorm_sq`
- `mem_annulus_imp_abs_gt`
- `annulus_indicator_le_wing`
- `sourceRootAnnularOutputWindow_tsum_le_concreteWingMajorant_of_root_decay`
- `sourceCompressedRoot_squareSum_of_rootConvolution_decay`
- `riemannHypothesis_of_right_rootConvolution_decay_and_aggregateEq`

## 3. Verification & Axioms

Audited in paired `...Audit` modules:
- Jobs: 4081 & 4082
- Error lines: 0
- `sorryAx`: 0
- Axioms: strictly standard Mathlib foundation `[propext, Classical.choice, Quot.sound]`.
