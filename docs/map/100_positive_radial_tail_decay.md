# 100 — Positive Radial Tail Reduction to Mathlib RiemannHypothesis

Date: 2026-09-23.
Status: FORMAL THEOREM COMPLETE (Lean 4 / standard axioms only).

## 1. Context & Placement

Building on Map 099 (`C1G8R3TranslatedKernelDecay`), which proved the isometric translation identity
`‖P_Q (T_t k0)‖^2 = ‖P_E (T_{-t} (Ht k0))‖^2`, this milestone record documents the complete reformulation
of both wings onto the positive ray $(N, \infty)$ in `ConnesWeilRH.Dev.C1G8R3PositiveRadialTailDecay`:

1. **Symmetric Wings Theorem**:
   `normSq_sourceSoninCarrier_starProjection_le_of_symmetric_wings` pairs left-wing Fourier decay on $t < -N$
   with right-wing radial decay on $t > N$, deducing uniform Sonin projection decay on $|t| > N$.

2. **Positive-Translation Radial Tails**:
   By substituting $s = -t > N$, the left-wing Fourier condition becomes an upper radial tail condition
   on the positive translation of the Hardy transform:
   $$\forall s > N, \|P_{\mathcal{E}} (T_s (Ht k_0))\|^2 \le \frac{C}{s^2}$$
   while the right-wing radial condition remains an upper radial tail on the positive translation of $k_0$:
   $$\forall t > N, \|P_{\mathcal{E}} (T_t k_0)\|^2 \le \frac{C}{t^2}$$

3. **Compact Support Vanishing Specialization**:
   When $k_0$ is compactly supported, its positive translation upper tail vanishes identically
   ($\|P_{\mathcal{E}} (T_t k_0)\| = 0$ for $t > N$).
   `riemannHypothesis_of_right_vanishing_compact_and_hardy_tail_and_aggregateEq` eliminates the right-wing
   estimate entirely, reducing unconditional Mathlib RH solely to the Hardy tail decay and the $\rho_5$ trace equality.

## 2. Core Lean Declarations

In `ConnesWeilRH.Dev.C1G8R3PositiveRadialTailDecay`:
- `normSq_sourceSoninCarrier_starProjection_le_of_symmetric_wings`
- `normSq_sourceSoninCarrier_starProjection_le_of_positive_radial_tails`
- `normSq_sourceSoninCarrier_starProjection_le_of_vanishing_right_tail`
- `sourceCompressedRoot_squareSum_of_positive_radial_tails`
- `sourceCompressedRoot_squareSum_of_vanishing_right_tail`
- `riemannHypothesis_of_right_positive_radial_tails_and_aggregateEq`
- `riemannHypothesis_of_right_vanishing_compact_and_hardy_tail_and_aggregateEq`

## 3. Verification & Axioms

Audited in `ConnesWeilRH.Dev.C1G8R3PositiveRadialTailDecayAudit`:
- Build log: `build-logs/1911_positive_radial_tail_decay.log`
- Jobs: 4085
- Errors: 0
- `sorryAx`: 0
- Axioms: strictly standard Mathlib foundation `[propext, Classical.choice, Quot.sound]`.
