# Record 1986 — Vertical Laplace decay, rung 1 LANDED: explicit 1/|w| bound, 15/15 standard axioms, constants valid not sharp

- **Date**: 2026-09-26
- **Status**: LANDED (Lean brick green; full build clean; axiom audit passed)
- **Brick**: `ConnesWeilRH/Dev/C1GevreyVerticalDecay.lean`
- **Audit**: `ConnesWeilRH/Dev/C1GevreyVerticalDecayAudit.lean` — all 15 public
  declarations report exactly `[propext, Classical.choice, Quot.sound]`;
  zero `sorryAx`, zero warnings.  Module build 8476 jobs, full build 4148
  jobs, both successful.

## 1. What landed

Rung 1 of the integration-by-parts (IBP) ladder toward brick 2's priced
target `|L_phi(a(sigma + i t))| <= C * exp(-c * sqrt(k |t|))` (record 1982;
constants valid-not-sharp per record 1983's ruling).  Two theorems:

    -- ConnesWeilRH/Dev/C1GevreyVerticalDecay.lean:357
    theorem laplace_abs_le (k : ℝ) (hk : 1 ≤ k) (w : ℂ) (hw : w ≠ 0) :
        ‖∫ u in (-1 : ℝ)..(1 : ℝ), (gevreyInner k u : ℂ) * Complex.exp (w * (u : ℂ))‖
            ≤ Real.exp |w.re| * (2 * Real.exp (-4 * k / 3) + 16 * k / 9 * Real.exp (-k)) / ‖w‖

    -- ConnesWeilRH/Dev/C1GevreyVerticalDecay.lean:473
    theorem laplace_abs_le_vertical (k a t : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ht : t ≠ 0) :
        ‖∫ u in (-1 : ℝ)..(1 : ℝ), (gevreyInner k u : ℂ) * Complex.exp ((a * t * Complex.I) * (u : ℂ))‖
            ≤ (2 * Real.exp (-4 * k / 3) + 16 * k / 9 * Real.exp (-k)) / (a * |t|)

The vertical form is the pipeline shape: at the pure-imaginary argument
`w = a * t * I` the strip factor `exp |Re w|` is exactly `1` and
`‖w‖ = a * |t|`, so the bound reads

    |L_phi(i a t)| <= (2 e^{-4k/3} + (16k/9) e^{-k}) / (a |t|).

## 2. Mechanism (why the constants are what they are)

    [ brick 1: window phi_k, flat at |u| = 1 ]
                |
                v
    [ gevreyDeriv: continuous piecewise derivative ]
      glue at |u| = 1 by squeeze through 2*6^6/k^5 * (1-u^2)^4,
      fed by exp(-k/t) = (exp(-k/(6t)))^6 <= (6t/k)^6
                |
                v
    [ exact L^1 mass of |phi_k'| ]
      outer halves: window monotone per half (sign of phi_k'),
      FTC gives the EXACT total variation e^{-4k/3} per half;
      middle |u| <= 1/2: quartic bound integrates to (16k/9) e^{-k}
                |
                v
    [ one IBP ]
      boundary terms phi_k(±1) = 0 (brick-1 flatness) kill the
      endpoints; |e^{wu}| <= e^{|Re w|} on [-1,1];
      1/|w| from dividing by the derivative of e^{wu}
                |
                v
    e^{|Re w|} (2 e^{-4k/3} + (16k/9) e^{-k}) / |w|

Evidence anchors: `integral_abs_gevreyDeriv_half_right/left`
(both `= Real.exp (-4*k/3)`), `integral_abs_gevreyDeriv_le`
(the `(16k/9) * exp(-k)` middle bound), `hasDerivAt_complex_gevreyInner`
(complex chain rule on the brick-1 inner function).

## 3. Honesty box

- **Rung 1 only.**  This is the `1/|w|` rung.  The priced brick-2 target is
  the `sqrt(k|t|)` law (record 1982); that needs the optimized-`n` rungs
  `n >= 2` of the IBP ladder, which are NOT here.
- **Constants valid, not sharp.**  Per record 1983's ruling the constants
  need only be valid; `2 e^{-4k/3} + (16k/9) e^{-k}` is far above the true
  saddle value at moderate `k` and decays exponentially in `k` — the
  `sqrt` law would give a faster `t`-decay via larger effective `n`, not
  via these constants.
- **No resolution certificate.**  Record 1985's second diagnosed gap (the
  quadrature aliasing floor of the finite sum) is untouched by this brick.
- **Support window fixed to [-1, 1].**  The scaling `phi_k(u/a)` generalization
  is not landed; the bound as stated is for the unit window.

## 4. Consequence for the lane

The 1985 failure analysis asked brick 2 to convert the true-transform tail
from "measured annulus" to "analytic bound".  Rung 1 delivers the analytic
bound in the weakest useful form: exponential-in-`k` numerator over linear
`|t|` denominator.  The route to the certified bracket remains:

    rung 1 (HERE) -> rungs n >= 2 (sqrt law) -> resolution certificate
                  -> re-bracket the 1985-class register.

No gate sign is proved here; RH is not claimed.
