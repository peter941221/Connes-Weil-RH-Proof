# 1912 — Compact Support Translation Vanishing for Radial Support Projection

Date: 2026-09-23.
Classification: FORMAL THEOREM (100% complete in Lean 4, standard axioms only).

## 1. Overview & Mathematical Architecture

In Record 1911 (`ConnesWeilRH.Dev.C1G8R3PositiveRadialTailDecay`), Mathlib's canonical `_root_.RiemannHypothesis`
was reduced to two positive-translation upper radial tail conditions on $t > N$:
- the physical root upper radial tail:
  $$\|P_{\mathcal{E}} (T_t k_0)\|^2 \le \frac{C}{t^2}$$
- the Hardy transform upper radial tail:
  $$\|P_{\mathcal{E}} (T_s (Ht k_0))\|^2 \le \frac{C}{s^2}$$

In this record (`ConnesWeilRH.Dev.C1G8R3CompactSupportRadialVanishing`), we formally discharge the physical root
condition by proving that for any compactly supported carrier vector $k_0$, its radial support projection under
sufficiently large positive translation is **identically zero**:
$$\forall t > R - \log \lambda, \quad P_{\mathcal{E}} (T_t k_0) = 0$$

### Mathematical Derivation:
1. **Subspace Characterization**:
   The radial support closed subspace $\mathcal{E}_\lambda$ is defined as the kernel of the restriction to $(-\infty, \log \lambda)$.
   Hence $v \in \mathcal{E}_\lambda \iff v(x) = 0$ for almost all $x < \log \lambda$.
2. **Disjoint Support Orthogonality**:
   If a vector $u \in L^2(\mathbb{R})$ vanishes almost everywhere on $[\log \lambda, \infty)$, then for any $v \in \mathcal{E}_\lambda$:
   $$u(x) \cdot v(x) = 0 \quad \text{a.e. on } \mathbb{R}$$
   Consequently:
   $$\langle u, v \rangle = \int_{\mathbb{R}} \overline{u(x)} v(x) dx = 0$$
   This proves that $u \in \mathcal{E}_\lambda^\perp$ (`mem_orthogonal_of_ae_eq_zero_on_Ici`).
3. **Exact Projection Vanishing**:
   By the orthogonal projection property (`orthogonalProjection_eq_zero_iff`), any vector in the orthogonal complement
   projects to zero:
   $$P_{\mathcal{E}} u = 0, \quad \|P_{\mathcal{E}} u\| = 0$$
4. **Translation Vanishing**:
   For $u = T_t k_0$, $(T_t k_0)(x) = k_0(x + t)$.
   When $x \ge \log \lambda$ and $t > R - \log \lambda$, we have:
   $$x + t \ge \log \lambda + t > R$$
   If $k_0$ has upper support bounded by $R$ ($k_0(y) = 0$ for $y > R$), then $k_0(x + t) = 0$ for all $x \ge \log \lambda$.
   Therefore:
   $$\|P_{\mathcal{E}} (T_t k_0)\| = 0 \quad \text{identically!}$$

## 2. Formal Lean Declarations

In `ConnesWeilRH.Dev.C1G8R3CompactSupportRadialVanishing`:
- `inner_eq_zero_of_ae_pointwise_zero`:
  $$(u(t), v(t)) = 0 \text{ a.e.} \implies \langle u, v \rangle = 0$$
- `inner_eq_zero_of_disjoint_support`:
  $$u|_{[\log \lambda, \infty)} = 0 \implies \forall v \in \mathcal{E}_\lambda, \langle u, v \rangle = 0$$
- `mem_orthogonal_of_ae_eq_zero_on_Ici`:
  $$u|_{[\log \lambda, \infty)} = 0 \implies u \in \mathcal{E}_\lambda^\perp$$
- `starProjection_eq_zero_of_ae_eq_zero_on_Ici`:
  $$u|_{[\log \lambda, \infty)} = 0 \implies P_{\mathcal{E}} u = 0$$
- `norm_starProjection_eq_zero_of_ae_eq_zero_on_Ici`:
  $$u|_{[\log \lambda, \infty)} = 0 \implies \|P_{\mathcal{E}} u\| = 0$$
- `norm_starProjection_translation_eq_zero_of_support_le`:
  $$\text{supp}(k_0) \le R \implies \forall t > R - \log \lambda, \|P_{\mathcal{E}} (T_t k_0)\| = 0$$
- `riemannHypothesis_of_right_compact_support_and_hardy_tail_and_aggregateEq`:
  Master Exit deducing Mathlib's canonical `_root_.RiemannHypothesis` with the right wing discharged by compact support vanishing.

## 3. Verification & Axioms

Audited in `ConnesWeilRH.Dev.C1G8R3CompactSupportRadialVanishingAudit`:
- Build log: `build-logs/1912_compact_support_vanishing.log`
- Jobs: 4086
- Errors: 0
- `sorryAx`: 0
- Axioms: strictly standard Mathlib foundation `[propext, Classical.choice, Quot.sound]`.
