# Map Record 102: Hardy Tail Moment Decay and Chebyshev Reduction to Mathlib RiemannHypothesis

**Date:** 2026-09-23
**Status:** FORMALIZED (Record 1913, Lean 4 / Mathlib v4.30.0 verified)
**Mainline Owner:** Healthy-`CompactLog` B5 mainline, G8 radial projection operator trace
**Source Code:**
- `ConnesWeilRH/Dev/C1G8R3HardyTailMomentDecay.lean`
- `ConnesWeilRH/Dev/C1G8R3HardyTailMomentDecayAudit.lean`

---

## 1. High-Level Route Architecture

Following the elimination of the compact-support right wing in Map 101, Map 102 establishes the exact mechanism for the upper radial tail decay of the archimedean Hardy--Titchmarsh transform:

```text
                  【Compact Support Right Wing: IDENTICALLY ZERO】
                  norm_starProjection_translation_eq_zero_of_support_le (Map 101)
                                      +
                  【Archimedean Hardy Tail: CHEBYSHEV MOMENT BOUND】
                  div_sq_shift_log_le_div_sq & pointwise_normSq_le_sq_mul_div_sq (Map 102)
                                      │
                                      ▼
                  【Master Exit to Mathlib RiemannHypothesis】
                  riemannHypothesis_of_right_compact_support_and_hardy_moment_and_aggregateEq
```

## 2. Quantitative Reduction

For any scale $\lambda \ge 1$ and shift $s > 0$:
1. $s \le s + \log \lambda \implies \frac{1}{(s + \log \lambda)^2} \le \frac{1}{s^2}$.
2. For $y \ge s + \log \lambda$, $\|w(y)\|^2 \le \frac{y^2 \|w(y)\|^2}{(s + \log \lambda)^2} \le \frac{y^2 \|w(y)\|^2}{s^2}$.
3. Integrating over the tail gives $\int_{s + \log \lambda}^\infty \|w(y)\|^2 dy \le \frac{M}{s^2}$, where $M = \int_0^\infty y^2 \|w(y)\|^2 dy$.
4. Any finite second moment $M \ge 0$ unconditionally supplies the required $O(1/s^2)$ tail decay.

## 3. Exit Integration

The master theorem `riemannHypothesis_of_right_compact_support_and_hardy_moment_and_aggregateEq` formally connects this second-moment formulation directly to Mathlib's canonical `_root_.RiemannHypothesis`.
Axioms: strictly standard `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.
