# Record 1988 — Vertical Laplace decay, rung 3 LANDED: explicit 1/|w|^3 bound with e^{-k}(9500k^3+19400k^2+6500k)+poly(k^{-4..-6}) numerator, 13/13 standard axioms

- **Date**: 2026-09-26
- **Status**: LANDED (Lean brick green; module + full build clean; axiom audit passed)
- **Brick**: `ConnesWeilRH/Dev/C1GevreyVerticalDecayRung3.lean`
- **Audit**: `ConnesWeilRH/Dev/C1GevreyVerticalDecayRung3Audit.lean` — all 13
  public declarations report exactly `[propext, Classical.choice, Quot.sound]`;
  zero `sorryAx`, zero new warnings.  Module build 8479 jobs, full build
  4148 jobs, both successful.
- **Numeric pre-check**: `scripts/check_rung3_math_1988.py` (mpmath, 40 dps)
  — all five checks PASS at k ∈ {1, 3, 30} before any Lean was written:
  the `phi'''` closed form matches the numerical third derivative to
  rel ~ 1e-41, and the total-mass bound holds with true/bound ratios
  9.3e-7 (k=1), 1.4e-5 (k=3), 6.5e-12 (k=30).

## 1. What landed

Rung 3 of the integration-by-parts (IBP) ladder toward brick 2's priced
target `|L_phi(a(sigma + i t))| <= C * exp(-c * sqrt(k |t|))` (record 1982).
Two theorems:

    theorem laplace_abs_le_rung3 (k : ℝ) (hk : 1 ≤ k) (w : ℂ) (hw : w ≠ 0) :
        ‖∫ u in (-1 : ℝ)..(1 : ℝ), (gevreyInner k u : ℂ) * Complex.exp (w * (u : ℂ))‖
            ≤ Real.exp |w.re| * (Real.exp (-k) * (9500 * k ^ 3 + 19400 * k ^ 2 + 6500 * k)
                + 2196115 * (k ^ 4)⁻¹ + 16470860 * (k ^ 5)⁻¹ + 19765032 * (k ^ 6)⁻¹)
              / ‖w‖ ^ 3

    theorem laplace_abs_le_rung3_vertical (k a t : ℝ) (hk : 1 ≤ k) (ha : 0 < a)
        (ht : t ≠ 0) :
        ‖∫ u in (-1 : ℝ)..(1 : ℝ),
            (gevreyInner k u : ℂ) * Complex.exp ((a * t * Complex.I) * (u : ℂ))‖
            ≤ (Real.exp (-k) * (9500 * k ^ 3 + 19400 * k ^ 2 + 6500 * k)
                + 2196115 * (k ^ 4)⁻¹ + 16470860 * (k ^ 5)⁻¹ + 19765032 * (k ^ 6)⁻¹)
              / (a * |t|) ^ 3

At the pure-imaginary argument the strip factor is exactly `1`, so the
vertical form reads `|L_phi(i a t)| <= N(k) / (a|t|)^3` — the same
`N(k)` numerator but one full power of `|t|` above rung 2.

## 2. Mechanism (why the constants are what they are)

    [ rung 2: two IBPs -> 1/|w|^2 ]
                |
                v
    [ third IBP: boundary terms killed by gevreyDeriv2 k (±1) = 0 (brick 1) ]
      u = gevreyDeriv2 k,  u' = gevreyDeriv3 k  (continuous piecewise 3rd deriv)
                |
                v
    [ phi''' closed form (odd in u; phi is even) ]
      e^{-k/s} (12k^2 u s^-4 - 8k^3 u^3 s^-6 + 48k^2 u^3 s^-5
                - 24 k u s^-3 - 48 k u^3 s^-4),  s = 1 - u^2
      formula verified vs numerical d^3/d u^3 at rel ~ 1e-41 (40 dps)
                |
                v
    [ SIGN FLIP on [5/6, 1) at k = 1:  +75.8, +77.0, +24.4, -116.0 ]
      => rung 2's FTC-exact outer mass trick (|phi''| of one sign) DROPPED;
      rung 3 is a PURE-BOUND brick: |phi'''| is bounded, never signed
                |
                v
    [ outer annulus 5/6 <= |u| < 1: the 7-power trade ]
      e^{-k/s} = (e^{-k/(7s)})^7 <= (7s/k)^7  (7s/k <= 1 there),
      the s^-6 term absorbs SIX s-powers, ONE survives:
      bound ~ 7^7 s |u|^3 k^-4 + ...  — vanishes at |u| = 1, so the
      continuity glue (value 0 outside) closes.
      (A 6-power trade would leave an s^0 constant and BREAK the glue.)
                |
                v
    [ septic universal bound, valid for ALL u ]
      bracket uses |u|^3 for the odd-u terms and even powers plain,
      so it is >= 0 for every u (also outside the window, where the
      |u| > 1 terms must be dominated);
      outer: int_{5/6}^1 <= 7^7 (8k^-4 + 60k^-5 + 72k^-6)/6  per side
                |
                v
    [ middle |u| <= 5/6: pointwise cap e^{-k} (5689k^3 + 11580k^2 + 3889k) ]
      exponential cap e^{-k} attained at u = 0 (s = 1), NOT the edge;
      rational ceilings: (5/3)*11580 -> 19400, (5/3)*5689 -> 9500,
      (5/3)*3889 -> 6500;  the k^2 ceiling needed
      ceil(10430*(11/36)^5) >= 250/9 — the first candidate 10429 is
      NUMERICALLY FALSE (27.77753 < 27.77778); caught before Lean.
                |
                v
    [ total L^1 mass: e^{-k}(9500k^3+19400k^2+6500k) + 2196115k^-4
                       + 16470860k^-5 + 19765032k^-6 ]
      exact coefficient arithmetic: (1/3)*7^7*8 = 6588344/3 <= 2196115,
      (1/3)*7^7*60 = 16470860 exact, (1/3)*7^7*72 = 19765032 exact
                |
                v
    [ three IBPs: 1/|w|^3 from dividing by (e^{wu})''' = w^3 e^{wu} ]
      |e^{wu}| <= e^{|Re w|} pointwise on [-1,1] (rung-1 lemma reused)

## 3. Honesty box

- **Rung 3 only.**  Fixed `n = 3`.  The priced brick-2 target (record 1982)
  is the `sqrt(k|t|)` law, which needs the optimized-`n` family
  `n ~ sqrt(k|t|)` with constants controlled uniformly in `n`; not here.
- **Constants valid, not sharp** (record 1983's ruling).  The total-mass
  bound sits a factor ~1e6 (k=1) to ~1e11 (k=30) above the true
  `int |phi'''|` (script check 4).  The looseness is concentrated in the
  outer annulus, where the 7-trade is brutal at small `k` (at `k = 1` the
  outer constant is ~3.8e7 against a true mass ~35.6).
- **k-behavior REGRESSION vs rung 2, traded for t-power.**  Rung 2's
  numerator was fully `e^{-k}`-capped: `(532k^2+398k) e^{-k}`.  Rung 3's
  outer part is the polynomial floor `2196115k^-4 + 16470860k^-5 +
  19765032k^-6`, which decays only like a power of `k` and dominates
  `e^{-k}`-scale truth beyond moderate `k`.  Dropping the FTC-exact outer
  (forced by the sign flip) is exactly what buys the third IBP.  The
  optimized-`n` rungs must repair the `k`-shape (the trade exponent grows
  with `n`, giving `k^{-Theta(n)}` floors — the `n ~ sqrt(k|t|)` choice is
  what converts them into the `sqrt` law).
- **No resolution certificate.**  Record 1985's second diagnosed gap (the
  quadrature aliasing floor `W ~ 1.27e18` on the `[8,24]` annulus) is
  untouched by this brick.
- **Support window fixed to [-1, 1]**; the `phi_k(u/a)` scaling
  generalization is not landed.  The `5/6` split is inherited from rung 2
  (proof device, not the phenomenon).

## 4. Consequence for the lane

The ladder now reads

    rung 1 (1986) -> rung 2 (1987) -> rung 3 (HERE)
                  -> rungs n >= 3 / optimized-n (sqrt law)
                  -> resolution certificate -> re-bracket the 1985-class register.

Rung 3 triples the `t`-decay power of the certified bound at the same
window and completes the fixed-`n` prefix of the ladder.  The brick also
fixes the rung-3-specific `HasDerivAt` chain (three `HasDerivAt.mul` /
`HasDerivAt.div` ascriptions with product-body functions) that the
`n >= 4` rungs will need; each further rung adds one derivative and two
more odd-power caps, so the marginal Lean cost is now calibrated.

No gate sign is proved here; RH is not claimed.
