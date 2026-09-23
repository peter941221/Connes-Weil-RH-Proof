# 099 — Translated Kernel Radial Tail Reduction to Mathlib RiemannHypothesis

Date: 2026-09-23.
Status: FORMAL THEOREM COMPLETE (Lean 4 / standard axioms only).

## 1. Context & Placement

Building on Map 098 (`C1G8R3KernelProjectionDecay`), which proved the two-sided cosine rule reducing Mathlib
`_root_.RiemannHypothesis` to left-wing radial decay on $t < -N$ and right-wing Fourier decay on $t > N$, this
record documents the reduction of the Fourier decay wing to a radial decay wing via Hardy--Titchmarsh conjugation.

1. **Hardy--Titchmarsh Translation Conjugation**:
   By `archimedeanHardyTitchmarsh_globalLogTranslation`, the unitary involution $Ht$ satisfies:
   $$Ht (T_t u) = T_{-t} (Ht u)$$
   Combining this with the definition of the Fourier support projection:
   $$P_{\mathcal{Q}} = Ht \circ P_{\mathcal{E}} \circ Ht$$
   yields the exact isometric identity (`sourceFourierSupportProjection_translation_norm_eq`):
   $$\|P_{\mathcal{Q}} (T_t k_0)\| = \|P_{\mathcal{E}} (T_{-t} (Ht k_0))\|$$

2. **Unified Radial Tail Decay**:
   Both wings are now reduced to evaluating the standard radial support projection $P_{\mathcal{E}}$:
   - For $t < -N$: evaluate $\|P_{\mathcal{E}} (T_t k_0)\|^2$;
   - For $t > N$: evaluate $\|P_{\mathcal{E}} (T_{-t} (Ht k_0))\|^2$.

3. **Master Exits**:
   - `sourceCompressedRoot_squareSum_of_translated_radial_tails`: discharges S3 survivor core square-summability.
   - `riemannHypothesis_of_right_translated_radial_tails_and_aggregateEq`: establishes unconditional RH from the radial tails of $k_0$ and $Ht(k_0)$ and the $\rho_5$ aggregate trace equality.

## 2. Core Lean Declarations

In `ConnesWeilRH.Dev.C1G8R3TranslatedKernelDecay`:
- `sourceFourierSupportProjection_apply`
- `norm_sourceFourierSupportProjection`
- `sourceFourierSupportProjection_translation_norm_eq`
- `sourceFourierSupportProjection_translation_normSq_eq`
- `normSq_sourceSoninCarrier_starProjection_le_of_translated_radial_tails`
- `sourceCompressedRoot_squareSum_of_translated_radial_tails`
- `riemannHypothesis_of_right_translated_radial_tails_and_aggregateEq`

## 3. Verification & Axioms

Audited in `ConnesWeilRH.Dev.C1G8R3TranslatedKernelDecayAudit`:
- Jobs: 4085
- Errors: 0
- `sorryAx`: 0
- Axioms: strictly standard Mathlib foundation `[propext, Classical.choice, Quot.sound]`.
