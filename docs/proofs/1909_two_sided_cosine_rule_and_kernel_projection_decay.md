# 1909 — Two-Sided Cosine Rule and Kernel Projection Decay to Mathlib RiemannHypothesis

Date: 2026-09-23.
Classification: FORMAL THEOREM (100% complete in Lean 4, standard axioms only).

## 1. Overview & Mathematical Architecture

In Record 1908 (`ConnesWeilRH.Dev.C1G8R3AnnularKernelPointwiseBound`), Mathlib's canonical `_root_.RiemannHypothesis`
was reduced to the unwindowed root convolution decay condition:
$$\forall t, N < |t| \implies \sum_i \|(rootConvolution owner (sourceInclusion lambda (sourceBasis i))) t\|_{\text{e}}^2 \le \frac{C}{t^2}$$
and the $\rho_5$ aggregate endpoint trace limit equality.

In Records 1733, 1734, and 1735, the two-sided cosine rule on the Sonin space:
$$\mathcal{S}_\lambda = \mathcal{E}_{\text{rad}} \cap \mathcal{Q}_{\text{Four}}$$
was proposed to control this kernel diagonal sum by decomposing into:
- a left wing ($t < -N$), controlled by the radial support projection $\mathcal{E}$;
- a right wing ($t > N$), controlled by the Fourier support projection $\mathcal{Q}$.

This module (`ConnesWeilRH.Dev.C1G8R3KernelProjectionDecay`) formally proves this entire architectural bridge:
1. **Submodule Containment**:
   - `sourceSoninCarrier_le_logRadialSupport`: $\mathcal{S}_\lambda \le \mathcal{E}$.
   - `sourceSoninCarrier_le_fourierSupport`: $\mathcal{S}_\lambda \le \mathcal{Q}$.

2. **Two-Sided Cosine Rule**:
   - `norm_sourceSoninCarrier_starProjection_le_logRadialSupport`:
     $$\|P_{\mathcal{S}} w\| \le \|P_{\mathcal{E}} w\|$$
   - `norm_sourceSoninCarrier_starProjection_le_fourierSupport`:
     $$\|P_{\mathcal{S}} w\| \le \|P_{\mathcal{Q}} w\|$$
   - `normSq_sourceSoninCarrier_starProjection_le_of_wings`:
     Combines radial decay on $t < -N$ and Fourier decay on $t > N$ into uniform Sonin projection decay:
     $$\forall t, N < |t| \implies \|P_{\mathcal{S}} (k_t)\|^2 \le \frac{C}{t^2}$$

3. **Bessel Identity & Unwindowed Root Decay**:
   - `rootConvolution_tsum_le_of_inner_kernel_projection_decay`:
     Given kernel pairing representation:
     $$(C u_i)(t) = \langle u_i, k_t \rangle$$
     applies `annular_kernelDiagonal_le_of_inner_kernel_projection_majorant` to deduce:
     $$\forall t, N < |t| \implies \sum_i \|(C u_i)(t)\|_{\text{e}}^2 \le \frac{C}{t^2}$$

4. **S3 Square-Summability & Master Exit**:
   - `sourceCompressedRoot_squareSum_of_kernel_projection_decay`:
     Discharges S3 survivor core square-summability from kernel projection decay.
   - `sourceCompressedRoot_squareSum_of_kernel_wing_decay`:
     Discharges S3 survivor core square-summability directly from separate left-wing (radial) and right-wing (Fourier) bounds.
   - `riemannHypothesis_of_right_kernel_wing_decay_and_aggregateEq`:
     Master Exit proving Mathlib `_root_.RiemannHypothesis` from the two-sided cosine rule wing estimates.

## 2. Formal Lean Declarations

In `ConnesWeilRH.Dev.C1G8R3KernelProjectionDecay`:
- `sourceSoninCarrier_le_logRadialSupport`
- `sourceSoninCarrier_le_fourierSupport`
- `norm_sourceSoninCarrier_starProjection_le_logRadialSupport`
- `norm_sourceSoninCarrier_starProjection_le_fourierSupport`
- `normSq_sourceSoninCarrier_starProjection_le_logRadialSupport`
- `normSq_sourceSoninCarrier_starProjection_le_fourierSupport`
- `normSq_sourceSoninCarrier_starProjection_le_of_wings`
- `rootConvolution_tsum_le_of_inner_kernel_projection_decay`
- `sourceCompressedRoot_squareSum_of_kernel_projection_decay`
- `sourceCompressedRoot_squareSum_of_kernel_wing_decay`
- `riemannHypothesis_of_right_kernel_wing_decay_and_aggregateEq`

## 3. Verification & Axioms

Audited in `ConnesWeilRH.Dev.C1G8R3KernelProjectionDecayAudit`:
- Build log: `build-logs/1909_kernel_projection_decay.log`
- Jobs: 4083
- Errors: 0
- `sorryAx`: 0
- Axioms: strictly standard Mathlib foundation `[propext, Classical.choice, Quot.sound]`.
