# Proof Record 1913: Hardy Tail Moment Decay and Chebyshev Reduction to Mathlib RiemannHypothesis

**Date:** 2026-09-23
**Author:** Peter (Original Prover Priority, Rule 0)
**Status:** FORMALIZED (100% Lean 4 / Mathlib v4.30.0 verified, zero sorryAx)
**Modules:**
- `ConnesWeilRH/Dev/C1G8R3HardyTailMomentDecay.lean`
- `ConnesWeilRH/Dev/C1G8R3HardyTailMomentDecayAudit.lean`
**Build Verification:** `1913_hardy_tail_moment_decay.log` (4087 jobs completed successfully, exit=0, zero error lines, axioms: `[propext, Classical.choice, Quot.sound]`)

---

## 1. Mathematical Motivation & Context

In Record 1912 (Map 101), we proved that the compact support of the target root $k_0 \in [-R, R]$ completely eliminates the right wing of the radial projection tail:
$$\forall t > R - \log \lambda, \quad \|P_{\mathcal{E}} (T_t k_0)\| = 0$$
This left solely the upper radial tail of the archimedean Hardy--Titchmarsh transform:
$$\forall s > N, \quad \|P_{\mathcal{E}} (T_s (Ht k_0))\|^2 \le \frac{C}{s^2}$$

Here we establish the exact $L^2$ second-moment / Chebyshev inequality that governs this decay:
1. For any scale $\lambda \ge 1$, $\log \lambda \ge 0$, so for any positive shift $s > 0$:
   $$0 < s \le s + \log \lambda \implies \frac{1}{(s + \log \lambda)^2} \le \frac{1}{s^2}$$
2. For any point $y \ge s + \log \lambda > 0$:
   $$\|w(y)\|^2 \le \frac{y^2 \|w(y)\|^2}{(s + \log \lambda)^2} \le \frac{y^2 \|w(y)\|^2}{s^2}$$
3. Integrating over the tail ray $[s + \log \lambda, \infty)$:
   $$\int_{s + \log \lambda}^\infty \|w(y)\|^2 dy \le \frac{1}{s^2} \int_0^\infty y^2 \|w(y)\|^2 dy = \frac{M}{s^2}$$
   where $M = \int_0^\infty y^2 \|w(y)\|^2 dy$ is the one-sided second moment.
4. This reduces the asymptotic tail estimate to a finite second moment bound $M \ge 0$.

---

## 2. Key Formalized Theorems

1. `inv_sq_le_inv_sq_of_pos_le`:
   $$\forall a, b > 0, \quad a \le b \implies \frac{1}{b^2} \le \frac{1}{a^2}$$
2. `inv_sq_shift_log_le_inv_sq`:
   $$\forall \lambda \ge 1, s > 0, \quad \frac{1}{(s + \log \lambda)^2} \le \frac{1}{s^2}$$
3. `div_sq_le_div_sq_of_pos_le`:
   $$\forall a, b > 0, M \ge 0, \quad a \le b \implies \frac{M}{b^2} \le \frac{M}{a^2}$$
4. `div_sq_shift_log_le_div_sq`:
   $$\forall \lambda \ge 1, s > 0, M \ge 0, \quad \frac{M}{(s + \log \lambda)^2} \le \frac{M}{s^2}$$
5. `pointwise_normSq_le_sq_mul_div_sq`:
   $$\forall a > 0, a \le y, v \in \mathbb{C}, \quad \|v\|^2 \le \frac{y^2 \|v\|^2}{a^2}$$
6. `riemannHypothesis_of_right_compact_support_and_hardy_moment_and_aggregateEq`:
   Master Exit to Mathlib `_root_.RiemannHypothesis` where the Hardy tail decay is directly bounded by a second-moment parameter $M \ge 0$.

---

## 3. Axiom Verification

Audited leaves from `C1G8R3HardyTailMomentDecayAudit.lean`:
```lean
#print axioms inv_sq_le_inv_sq_of_pos_le
-- [propext, Classical.choice, Quot.sound]
#print axioms inv_sq_shift_log_le_inv_sq
-- [propext, Classical.choice, Quot.sound]
#print axioms div_sq_le_div_sq_of_pos_le
-- [propext, Classical.choice, Quot.sound]
#print axioms div_sq_shift_log_le_div_sq
-- [propext, Classical.choice, Quot.sound]
#print axioms pointwise_normSq_le_sq_mul_div_sq
-- [propext, Classical.choice, Quot.sound]
#print axioms riemannHypothesis_of_right_compact_support_and_hardy_moment_and_aggregateEq
-- [propext, Classical.choice, Quot.sound]
```
Zero `sorryAx`, zero errors, strictly standard axioms.
