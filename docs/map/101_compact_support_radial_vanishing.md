# 101 — Compact Support Translation Vanishing for Radial Support Projection

Date: 2026-09-23.
Status: FORMAL THEOREM COMPLETE (Lean 4 / standard axioms only).

## 1. Context & Placement

Building on Map 100 (`C1G8R3PositiveRadialTailDecay`), which formulated the two-wing Sonin projection decay
on the positive ray $(N, \infty)$ and established the conditional vanishing exit
`riemannHypothesis_of_right_vanishing_compact_and_hardy_tail_and_aggregateEq`, this record documents
the formal closure of the compact support vanishing theorem in `ConnesWeilRH.Dev.C1G8R3CompactSupportRadialVanishing`:

1. **Disjoint Support Orthogonality**:
   Proves that any function vanishing almost everywhere on $[\log \lambda, \infty)$ is strictly orthogonal
   to the radial support closed subspace $\mathcal{E}_\lambda$ (`mem_orthogonal_of_ae_eq_zero_on_Ici`),
   and therefore has zero orthogonal projection:
   $$P_{\mathcal{E}} u = 0, \quad \|P_{\mathcal{E}} u\| = 0$$

2. **Translation Support Propagation**:
   For any vector $k_0$ supported below $R$ ($k_0(y) = 0$ for $y > R$), translation by $t > R - \log \lambda$
   shifts its support strictly below $\log \lambda$. Hence:
   $$\forall t > R - \log \lambda, \quad \|P_{\mathcal{E}} (T_t k_0)\| = 0$$

3. **Discharge of Right Wing**:
   This completely discharges the right-wing decay condition for any compactly supported test.
   The master exit `riemannHypothesis_of_right_compact_support_and_hardy_tail_and_aggregateEq`
   proves that Mathlib's canonical `_root_.RiemannHypothesis` follows from:
   - Upper support bound on $k_0$: $k_0(y) = 0$ for $y \ge N - \log \lambda$;
   - Upper radial tail bound on Hardy transform $Ht(k_0)$: $\|P_{\mathcal{E}} (T_s (Ht k_0))\|^2 \le C / s^2$ for $s > N$;
   - The $\rho_5$ aggregate trace equality.

## 2. Core Lean Declarations

In `ConnesWeilRH.Dev.C1G8R3CompactSupportRadialVanishing`:
- `inner_eq_zero_of_ae_pointwise_zero`
- `inner_eq_zero_of_disjoint_support`
- `mem_orthogonal_of_ae_eq_zero_on_Ici`
- `starProjection_eq_zero_of_ae_eq_zero_on_Ici`
- `norm_starProjection_eq_zero_of_ae_eq_zero_on_Ici`
- `norm_starProjection_translation_eq_zero_of_support_le`
- `riemannHypothesis_of_right_compact_support_and_hardy_tail_and_aggregateEq`

## 3. Verification & Axioms

Audited in `ConnesWeilRH.Dev.C1G8R3CompactSupportRadialVanishingAudit`:
- Build log: `build-logs/1912_compact_support_vanishing.log`
- Jobs: 4086
- Errors: 0
- `sorryAx`: 0
- Axioms: strictly standard Mathlib foundation `[propext, Classical.choice, Quot.sound]`.
