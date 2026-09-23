# 1910 — Translated Kernel Radial Tail Reduction to Mathlib RiemannHypothesis

Date: 2026-09-23.
Classification: FORMAL THEOREM (100% complete in Lean 4, standard axioms only).

## 1. Overview & Mathematical Architecture

In Record 1909 (`ConnesWeilRH.Dev.C1G8R3KernelProjectionDecay`), Mathlib's canonical `_root_.RiemannHypothesis`
was reduced via the two-sided cosine rule to two separate wing bounds on the kernel vector family $k_t$:
- a left-wing radial projection bound on $t < -N$:
  $$\|P_{\mathcal{E}} (k_t)\|^2 \le \frac{C}{t^2}$$
- a right-wing Fourier projection bound on $t > N$:
  $$\|P_{\mathcal{Q}} (k_t)\|^2 \le \frac{C}{t^2}$$

In this record (`ConnesWeilRH.Dev.C1G8R3TranslatedKernelDecay`), we specialize $k_t$ to the translated orbit
$k_t = T_t k_0$, where $T_t = \text{cc20GlobalLogTranslation } t$. Using the isometric Hardy--Titchmarsh involution
$Ht$ (`archimedeanHardyTitchmarshOperator`) and its commutation relation with translation:
$$Ht(T_t u) = T_{-t} (Ht u)$$
and the definition of the Fourier support projection:
$$P_{\mathcal{Q}} = Ht \circ P_{\mathcal{E}} \circ Ht$$
we prove that the Fourier support projection of $T_t k_0$ is *identically equal* in norm to the radial support
projection of the opposite translation of $Ht(k_0)$:
$$\|P_{\mathcal{Q}} (T_t k_0)\| = \|P_{\mathcal{E}} (T_{-t} (Ht k_0))\|$$

Consequently, both the left wing and the right wing are completely governed by the **same radial support projection**
$P_{\mathcal{E}}$ acting on two fixed vectors:
1. $k_0 \in \mathcal{H}$ (for $t < -N$);
2. $Ht(k_0) \in \mathcal{H}$ (for $t > N$).

## 2. Formal Lean Declarations

In `ConnesWeilRH.Dev.C1G8R3TranslatedKernelDecay`:
- `sourceFourierSupportProjection_apply`:
  $$P_{\mathcal{Q}} u = Ht (P_{\mathcal{E}} (Ht u))$$
- `norm_sourceFourierSupportProjection`:
  $$\|P_{\mathcal{Q}} u\| = \|P_{\mathcal{E}} (Ht u)\|$$
- `sourceFourierSupportProjection_translation_norm_eq`:
  $$\|P_{\mathcal{Q}} (T_t k_0)\| = \|P_{\mathcal{E}} (T_{-t} (Ht k_0))\|$$
- `sourceFourierSupportProjection_translation_normSq_eq`:
  $$\|P_{\mathcal{Q}} (T_t k_0)\|^2 = \|P_{\mathcal{E}} (T_{-t} (Ht k_0))\|^2$$
- `normSq_sourceSoninCarrier_starProjection_le_of_translated_radial_tails`:
  Unifies both wings to show:
  $$\forall t, N < |t| \implies \|P_{\mathcal{S}} (T_t k_0)\|^2 \le \frac{C}{t^2}$$
- `sourceCompressedRoot_squareSum_of_translated_radial_tails`:
  Discharges S3 survivor core square-summability from translated radial tails.
- `riemannHypothesis_of_right_translated_radial_tails_and_aggregateEq`:
  Master Exit deducing Mathlib's canonical `_root_.RiemannHypothesis` from:
  1. Left-wing radial tail: $\|P_{\mathcal{E}} (T_t k_0)\|^2 \le C / t^2$ for $t < -N$;
  2. Right-wing radial tail: $\|P_{\mathcal{E}} (T_{-t} (Ht k_0))\|^2 \le C / t^2$ for $t > N$;
  3. The $\rho_5$ aggregate trace equality.

## 3. Verification & Axioms

Audited in `ConnesWeilRH.Dev.C1G8R3TranslatedKernelDecayAudit`:
- Build log: `build-logs/1910_translated_kernel_decay.log`
- Jobs: 4085
- Errors: 0
- `sorryAx`: 0
- Axioms: strictly standard Mathlib foundation `[propext, Classical.choice, Quot.sound]`.
