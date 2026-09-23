# 098 — Two-Sided Cosine Rule and Kernel Projection Decay to Mathlib RiemannHypothesis

Date: 2026-09-23.
Status: FORMAL THEOREM COMPLETE (Lean 4 / standard axioms only).

## 1. Context & Placement

Building on Map 097 (`C1G8R3AnnularKernelPointwiseBound`), which reduced Mathlib's `_root_.RiemannHypothesis`
to the unwindowed root convolution decay condition:
$$\forall t, N < |t| \implies \sum_i \|(\mathcal{K}_{\text{root}} e_i)(t)\|_{\text{e}}^2 \le \frac{C}{t^2}$$

this record documents the completion of the two-sided cosine rule reduction and kernel projection decay
bridge in `ConnesWeilRH.Dev.C1G8R3KernelProjectionDecay`:

1. **Submodule Projection Cosine Rule**:
   Proves that the source Sonin carrier $\mathcal{S}_\lambda$ satisfies $\mathcal{S}_\lambda \le \mathcal{E}$ (log radial support)
   and $\mathcal{S}_\lambda \le \mathcal{Q}$ (Fourier support). By the orthogonal projection cosine rule
   (`norm_starProjection_le_of_submodule_le`), for every vector $w \in \mathcal{H}$:
   $$\|P_{\mathcal{S}} w\| \le \|P_{\mathcal{E}} w\| \quad \text{and} \quad \|P_{\mathcal{S}} w\| \le \|P_{\mathcal{Q}} w\|$$

2. **Wing Assembly**:
   Proves `normSq_sourceSoninCarrier_starProjection_le_of_wings`: combining left-wing radial decay on $t < -N$
   and right-wing Fourier decay on $t > N$ establishes uniform projection decay:
   $$\forall t, N < |t| \implies \|P_{\mathcal{S}} (k_t)\|^2 \le \frac{C}{t^2}$$

3. **Bessel Identity Bridge**:
   `rootConvolution_tsum_le_of_inner_kernel_projection_decay` applies Bessel's identity to prove that
   if $(C u_i)(t) = \langle u_i, k_t \rangle$, then the unwindowed root convolution diagonal sum is bounded by $C / t^2$.

4. **Master Exits**:
   - `sourceCompressedRoot_squareSum_of_kernel_wing_decay`: discharges S3 survivor core square-summability.
   - `riemannHypothesis_of_right_kernel_wing_decay_and_aggregateEq`: deduces Mathlib's canonical `_root_.RiemannHypothesis`.

## 2. Core Lean Declarations

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
- Jobs: 4083
- Error lines: 0
- `sorryAx`: 0
- Axioms: strictly standard Mathlib foundation `[propext, Classical.choice, Quot.sound]`.
