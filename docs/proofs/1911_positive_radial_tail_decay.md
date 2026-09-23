# 1911 — Positive Radial Tail Reduction to Mathlib RiemannHypothesis

Date: 2026-09-23.
Classification: FORMAL THEOREM (100% complete in Lean 4, standard axioms only).

## 1. Overview & Mathematical Architecture

In Record 1910 (`ConnesWeilRH.Dev.C1G8R3TranslatedKernelDecay`), the Sonin projection decay outside `[-N, N]`
was reduced to two radial support projection estimates on translated orbits:
- a left-wing bound for $t < -N$:
  $$\|P_{\mathcal{E}} (T_t k_0)\|^2 \le \frac{C}{t^2}$$
- a right-wing bound for $t > N$:
  $$\|P_{\mathcal{E}} (T_{-t} (Ht k_0))\|^2 \le \frac{C}{t^2}$$

In this record (`ConnesWeilRH.Dev.C1G8R3PositiveRadialTailDecay`), we reformulate both wings to be evaluated
**strictly on the positive half-line** $(N, \infty)$, establishing the natural mathematical alignment of the two projections:
1. **Symmetric Wings Theorem**:
   `normSq_sourceSoninCarrier_starProjection_le_of_symmetric_wings` proves that Sonin projection decay is
   established whenever the left wing ($t < -N$) is controlled by Fourier projection $P_{\mathcal{Q}}$ and the
   right wing ($t > N$) is controlled by radial projection $P_{\mathcal{E}}$.
2. **Positive-Translation Radial Tails**:
   `normSq_sourceSoninCarrier_starProjection_le_of_positive_radial_tails` combines the symmetric wing theorem
   with the Hardy translation identity:
   $$\|P_{\mathcal{Q}} (T_t k_0)\|^2 = \|P_{\mathcal{E}} (T_{-t} (Ht k_0))\|^2$$
   Setting $s = -t > N$, the left-wing Fourier condition becomes an upper radial tail of $Ht(k_0)$ on $s > N$:
   $$\forall s > N, \|P_{\mathcal{E}} (T_s (Ht k_0))\|^2 \le \frac{C}{s^2}$$
   while the right-wing radial condition is an upper radial tail of $k_0$ on $t > N$:
   $$\forall t > N, \|P_{\mathcal{E}} (T_t k_0)\|^2 \le \frac{C}{t^2}$$
3. **Vanishing Compact Support Specialization**:
   `normSq_sourceSoninCarrier_starProjection_le_of_vanishing_right_tail` and
   `riemannHypothesis_of_right_vanishing_compact_and_hardy_tail_and_aggregateEq`
   specialize to the case where the right-wing radial projection vanishes identically
   ($\|P_{\mathcal{E}} (T_t k_0)\| = 0$ for $t > N$, as guaranteed by the compact support of $k_0$),
   leaving **solely the Hardy tail decay condition on $s > N$**.

## 2. Formal Lean Declarations

In `ConnesWeilRH.Dev.C1G8R3PositiveRadialTailDecay`:
- `normSq_sourceSoninCarrier_starProjection_le_of_symmetric_wings`:
  $$\forall t, N < |t| \implies \|P_{\mathcal{S}} (k_t)\|^2 \le \frac{C}{t^2}$$
- `normSq_sourceSoninCarrier_starProjection_le_of_positive_radial_tails`:
  Sonin projection decay from positive radial tails of $k_0$ and $Ht(k_0)$.
- `normSq_sourceSoninCarrier_starProjection_le_of_vanishing_right_tail`:
  Sonin projection decay when the right-wing radial projection vanishes identically.
- `sourceCompressedRoot_squareSum_of_positive_radial_tails`:
  Discharges S3 survivor core square-summability from positive radial tails.
- `sourceCompressedRoot_squareSum_of_vanishing_right_tail`:
  Discharges S3 survivor core when the right wing vanishes identically.
- `riemannHypothesis_of_right_positive_radial_tails_and_aggregateEq`:
  Master Exit deducing Mathlib's canonical `_root_.RiemannHypothesis` from positive radial tails and the $\rho_5$ aggregate trace equality.
- `riemannHypothesis_of_right_vanishing_compact_and_hardy_tail_and_aggregateEq`:
  Master Exit deducing Mathlib's canonical `_root_.RiemannHypothesis` where the compact support right wing is completely eliminated.

## 3. Verification & Axioms

Audited in `ConnesWeilRH.Dev.C1G8R3PositiveRadialTailDecayAudit`:
- Build log: `build-logs/1911_positive_radial_tail_decay.log`
- Jobs: 4085
- Errors: 0
- `sorryAx`: 0
- Axioms: strictly standard Mathlib foundation `[propext, Classical.choice, Quot.sound]`.
