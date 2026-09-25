# Record 1987 — Vertical Laplace decay, rung 2 LANDED: explicit 1/|w|^2 bound with (532k^2+398k)e^{-k} numerator, 16/16 standard axioms

- **Date**: 2026-09-26
- **Status**: LANDED (Lean brick green; module + full build clean; axiom audit passed)
- **Brick**: `ConnesWeilRH/Dev/C1GevreyVerticalDecayRung2.lean`
- **Audit**: `ConnesWeilRH/Dev/C1GevreyVerticalDecayRung2Audit.lean` — all 16
  public declarations report exactly `[propext, Classical.choice, Quot.sound]`;
  zero `sorryAx`, zero new warnings.  Module build 8477 jobs, full build
  4148 jobs, both successful.
- **Numeric pre-check**: `scripts/check_rung2_math_1987.py` (mpmath, 40 dps)
  — all six hand-derivation checks PASS at k ∈ {1, 3, 30} before any Lean
  was written; the self-check caught a wrong exponential cap
  (`e^{-36k/11}` → `e^{-k}`, attained at u = 0) in the middle bound.

## 1. What landed

Rung 2 of the integration-by-parts (IBP) ladder toward brick 2's priced
target `|L_phi(a(sigma + i t))| <= C * exp(-c * sqrt(k |t|))` (record 1982).
Two theorems:

    theorem laplace_abs_le_rung2 (k : ℝ) (hk : 1 ≤ k) (w : ℂ) (hw : w ≠ 0) :
        ‖∫ u in (-1 : ℝ)..(1 : ℝ), (gevreyInner k u : ℂ) * Complex.exp (w * (u : ℂ))‖
            ≤ Real.exp |w.re| * ((532 * k ^ 2 + 398 * k) * Real.exp (-k)) / ‖w‖ ^ 2

    theorem laplace_abs_le_rung2_vertical (k a t : ℝ) (hk : 1 ≤ k) (ha : 0 < a)
        (ht : t ≠ 0) :
        ‖∫ u in (-1 : ℝ)..(1 : ℝ),
            (gevreyInner k u : ℂ) * Complex.exp ((a * t * Complex.I) * (u : ℂ))‖
            ≤ (532 * k ^ 2 + 398 * k) * Real.exp (-k) / (a * |t|) ^ 2

The vertical form is the pipeline shape: at the pure-imaginary argument the
strip factor is exactly `1`, so `|L_phi(i a t)| <= (532 k^2 + 398 k) e^{-k} /
(a|t|)^2` — the same numerator as rung 1's `(2 e^{-4k/3} + (16k/9) e^{-k})`
family but now over `|t|^2` instead of `|t|`, and with an `e^{-k}` cap on the
whole constant instead of an `e^{-4k/3}` half.

## 2. Mechanism (why the constants are what they are)

    [ rung 1: one IBP, boundary terms killed by phi_k(±1) = 0 ]
                |
                v
    [ second IBP: boundary terms killed by gevreyDeriv k (±1) = 0 (brick 1) ]
      u = gevreyDeriv k, u' = gevreyDeriv2 k  (continuous piecewise 2nd deriv)
                |
                v
    [ gevreyDeriv2 sign structure: the split point 5/6 ]
      phi'' >= 0 on [5/6, 1) for ALL k >= 1  <=>  s^2 + 4 s u^2 <= 2 k u^2
      with s = 1 - u^2 <= 11/36, u >= 5/6:  LHS <= (121/900 + 44/36) u^2
      = (11/36 + 44/36) u^2 = 55/36 u^2 <= 2 u^2 <= 2 k u^2.
      At 1/2 the sign flips for small k, so 5/6 is the largest rational
      split with a fixed sign for all k >= 1.
                |
                v
    [ exact outer L^1 mass via FTC ]
      antitone-outer: int_{5/6}^1 |phi''| = |phi'(5/6)| = (2160 k/121) e^{-36k/11}
      (36/11 ≈ 3.27 — much faster than rung 1's e^{-4k/3})
                |
                v
    [ middle |u| <= 5/6: pointwise e^{-k} (22k + 195k + 319k^2) ]
      exponential cap e^{-k} attained at u = 0 (s = 1), NOT the edge value
      e^{-36k/11} — the erratum the 40-dps self-check caught;
      rational constant bounds: (11/36)^2 <= s^2 <= 1, 4(25/36) <= 319(11/36)^4,
      8(25/36) <= 195(11/36)^3; (22k + 195k + 319k^2)(5/3) <= 362k + 532k^2
                |
                v
    [ total L^1 mass: (532 k^2 + 398 k) e^{-k} ]
      outer 4320k/121 <= 36k gives the 398k = 362k + 36k split
                |
                v
    [ two IBPs: 1/|w|^2 from dividing by (e^{wu})'' = w^2 e^{wu} ]
      |e^{wu}| <= e^{|Re w|} pointwise on [-1,1] (rung-1 lemma reused)

## 3. Honesty box

- **Rung 2 only.**  This is the `1/|w|^2` rung with FIXED `n = 2`.  The
  priced brick-2 target (record 1982) is the `sqrt(k|t|)` law, which needs
  the optimized-`n` rungs `n >= 3` (choosing `n ~ sqrt(k|t|)`); not here.
- **Constants valid, not sharp.**  Per record 1983's ruling.  The true
  saddle mass of `|phi''|` is far below `(532k^2+398k) e^{-k}` at moderate
  `k` (the middle pointwise bound alone is within a constant factor, but the
  outer/middle split discards cancellation).
- **No resolution certificate.**  Record 1985's second diagnosed gap (the
  quadrature aliasing floor of the finite sum) is untouched by this brick.
- **Support window fixed to [-1, 1]**; the scaling `phi_k(u/a)` generalization
  is not landed.
- **5/6 split is for the proof, not the phenomenon.**  The sign structure of
  `phi''` genuinely changes near `u ~ 1/2` for `k ~ 1`; a k-dependent split
  would sharpen the constants but complicates the rational bookkeeping.

## 4. Consequence for the lane

The ladder now reads

    rung 1 (1986) -> rung 2 (HERE) -> rungs n >= 3 / optimized-n (sqrt law)
                  -> resolution certificate -> re-bracket the 1985-class register.

Rung 2 doubles the `t`-decay power of the certified bound at the same
window.  The remaining gap to the priced target is qualitative: an
`n`-dependent family of rungs with constants controlled uniformly in `n`
would let `n ~ sqrt(k|t|)` beat `e^{-k}` against `|t|^{-N}` for any fixed
`N`, which is what the bracket's `t`-tail needs.

No gate sign is proved here; RH is not claimed.
