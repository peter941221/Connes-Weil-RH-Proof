# Record 1976: The third rung is a certified rational bracket, not a transcendental constant

Date: 2026-09-25

## Closed

1. The exp machinery. On `[0, 1]` the order-20 Taylor polynomial of `exp` at
   `0` together with the Lagrange tail gives certified rational two-sided
   bounds for `e^w` at any rational `w`, in the power form

       (expTaylor (w / m) - expTail (w / m)) ^ m <= Real.exp w
         <= (expTaylor (w / m) + expTail (w / m)) ^ m

   for `0 <= w`, `m >= 1`, `w <= m` (`exp_bounds_pow`), where
   `expTaylor y = sum_{k<20} y^k/k!` and `expTail y = y^20/20! * 20/19`
   (the Lagrange remainder at an interior point, bounded by the endpoint
   value). This avoids real exponentiation by a non-integer rational: the
   power is a natural-number power of a rational.

2. The logistic enclosure. With the exponential argument
   `seedV s = 4 s / (1 - s^2)` and the logistic value
   `seedU s = (e^{v s} - 1) / (e^{v s} + 1)` (equal to `tanh (v s / 2)`), the
   power enclosure transfers through the increasing ratio `x -> (x-1)/(x+1)`
   to

       seedULo s m <= seedU s <= seedUHi s m

   for every `0 <= s < 1` with `seedV s <= m` and `1 <= m`
   (`seedU_mem_Icc`), where `seedULo`/`seedUHi` are rational functions of the
   rational `seedExpLo`/`seedExpHi` bounds. Both sides are explicit rational
   numbers of `s` and `m`.

3. The bracket enclosure. The committed `T'''` closed form is
   `(1 - s^2)^6 * T'''((1-s)/2) = 64 * T x (1 - T x) * P (s, u)` with
   `u = 1 - 2 T x = seedU s` and `P` the quadratic
   `thirdOrderLeading s * u^2 - thirdOrderMiddle s * u + thirdOrderConstant s`
   (record 1975). Writing the three coefficients' elementary symmetric
   expansions and their interval monotonicity on `[a, b]` with `0 <= a`,
   `b <= 1`, any rational sandwich `uL <= seedU s <= uH` on `s in [a, b]`
   encloses the bracket profile:

       seedBracket s ∈ Set.Icc (seedBracketLower a b uL uH)
                            (seedBracketUpper a b uL uH)

   (`seedBracket_mem_Icc`), where `seedBracket s = P (s, seedU s)`. Every
   side is a rational number when `a`, `b`, `uL`, `uH` are rational.

4. The partition. The interval `(0, 1)` is covered by 37 rational pieces:

       [0, 11/20]     22 pieces  L01 .. L22   (bracket < 0)
       [11/20, 23/40] the straddle           (strictly increasing)
       [23/40, 1)     15 pieces  R01 .. R15   (bracket > 0)

   Each piece is a theorem `seedBracket_neg_L01 ... L22`,
   `seedBracket_pos_R01 ... R15` proved by `norm_num` on the explicit
   rational enclosure (with the piece-dependent exponent `m` chosen so that
   `seedV s <= m` on the piece), and the chains assemble by trichotomy into

       seedBracket_neg_of_Icc_zero_s_lo :
         s ∈ [0, 11/20]  ->  seedBracket s < 0,
       seedBracket_pos_of_Ico_s_hi_one :
         s ∈ [23/40, 1)  ->  0 < seedBracket s.

5. The straddle. On `[11/20, 23/40]` the total derivative of the bracket
   along the curve, split as

       h' (s) = alpha' (s) u^2 - beta' (s) u + gamma' (s)
                  + (2 alpha (s) u - beta (s)) u' (s)

   (from the product split of the two-variable derivative), is bounded below
   by the explicit rational constant

       seedHprimeLower = alpha' (11/20) * uL^2 - beta' (11/20) * uH
                           + gamma' (23/40)
                           + (2 alpha (11/20) * uL - beta (23/40))
                               * (seedVSlope (11/20) / 2) * (1 - uH^2)

   with `uL = seedULo (11/20) 4`, `uH = seedUHi (23/40) 4`: the two terms are
   `+1.869140038...` and `+18.264149737...`, so `seedHprimeLower >=
   20.1332897756 > 0`. Hence `seedBracket` is strictly increasing on the
   straddle (`seedBracket_strictMonoOn`), and the two rational point values

       seedBracket (5634883/10^7) < 0,      seedBracket (1408721/2500000) > 0

   straddle the unique zero:

       existsUnique_seedBracket_eq_zero :
         ∃! s, s ∈ [5634883/10^7, 1408721/2500000] ∧ seedBracket s = 0.

   Monotonicity then upgrades the two chains to the global sign split

       seedBracket_neg_of_Icc_zero_s_d : s ∈ [0, 5634883/10^7] -> P s < 0,
       seedBracket_pos_of_Ico_s_c_one : s ∈ [1408721/2500000, 1) -> P s > 0.

6. The sign transfer to `T'''`. The committed closed form rewrites on the
   left half `x = (1 - s)/2` as

       (1 - s^2)^6 * T'''((1 - s)/2) = 64 * T x * (1 - T x) * seedBracket s

   (`iteratedDeriv_three_smoothTransition_eq_seedBracket`), with the prefactor
   strictly positive; hence

       T'''((1-s)/2) > 0  on  s ∈ [1408721/2500000, 1)  (x ∈ (0, x_c]),
       T'''((1-s)/2) < 0  on  s ∈ [0, 5634883/10^7]     (x ∈ [x_d, 1/2)),

   with `x_c = 1091279/5000000`, `x_d = 4365117/20000000`
   (`iteratedDeriv_three_pos_of_Ioc_zero_x_c`,
   `_neg_of_Ico_x_d_half`, `_nonneg_of_Icc_zero_x_c`,
   `_nonpos_of_Icc_x_d_half`). This is the certified form of "the third
   derivative has exactly one sign change on the left half, at `x*` in
   `(x_d, x_c)`".

7. The rung. `derivOrderL1 3 smoothSeed` is four times the absolute mass of
   `T'''` on `(0, 1/2)`. Splitting at the certified points and using the sign
   knowledge,

       ∫_{x_d}^{1/2} |T'''| = T'' (x_d),
       ∫_{0}^{x_c} |T'''| = T'' (x_c)

   (fundamental theorem of calculus with a sign-definite integrand), and the
   middle piece `[x_c, x_d]` of width `1/20000000` is bounded by the gap
   constant

       |T''' y| <= gapBound := 16 * |gapHi| / (1 - (1408721/2500000)^2)^6
         for y ∈ [x_c, x_d]      (`iteratedDeriv_three_abs_le_gapBound`),

   where `gapHi = seedBracketUpper (5634883/10^7) (1408721/2500000) uL uH` is
   the two-point bracket enclosure of the profile in the gap. `T''` itself is
   bracketed by a Lipschitz evaluation of the committed polynomial
   `T''((1-s)/2) = p (seedU s)/4` with `p (u) = (1 - u^2)(u G^2 + G')`:

       T''((1-s)/2) ∈ Set.Icc (ttwoLower s) (ttwoUpper s)
         (`iteratedDeriv_two_smoothTransition_mem_Icc`).

   Assembling,

       derivOrderL1 3 smoothSeed ∈ Set.Icc (787283384 / 10^7) (787283385 / 10^7)

   (`derivOrderL1_smoothSeed_three_mem_Icc`): the third rung, previously the
   transcendental constant `8 * T'' x*` with only the certified half
   `4 * T'' x <= derivOrderL1 3 smoothSeed` (1974), is now a certified
   rational bracket of width `1e-7`. The bracket contains the probe value
   `78.7283384146...` and hence also supplies the matching upper bound for
   the committed lower bound.

8. A rational bracket on `x*` falls out with no extra work: the crossings
   `x* = (1 - s*)/2` with `s* ∈ (5634883/10^7, 1408721/2500000)` give

       0.21825580 < x* < 0.21825585,

   width `5e-8`, containing the probe's `x* = 0.218255829186` (1974/1975).

## Evidence

- Module `ConnesWeilRH/Dev/C1ExplicitSeedThirdOrderIntervalCertificate.lean`
  (2175 lines, 131 declarations), audit
  `C1ExplicitSeedThirdOrderIntervalCertificateAudit.lean` (131 `#print axioms`).
- Build (sanctioned resource-aware runner, WSL ext4 mirror):

      lake build ConnesWeilRH.Dev.C1ExplicitSeedThirdOrderIntervalCertificate \
                 ConnesWeilRH.Dev.C1ExplicitSeedThirdOrderIntervalCertificateAudit

  log `build-logs/1976_interval_certificate_build4.log`:
  `Build completed successfully (3654 jobs)`, `grep -c error` = 0,
  `grep -c sorryAx` = 0, and no warning line mentions either new module.
  All 131 declarations print exactly
  `[propext, Classical.choice, Quot.sound]`.

- The certified constants (exact rationals in Lean; decimals from the rig for
  orientation only):

  +------------------------------------------------+--------------------------+
  | quantity                                        | value                    |
  +------------------------------------------------+--------------------------+
  | straddle lower constant `seedHprimeLower`       | >= 20.133289775606221832 |
  |   term `alpha' u^2 - beta' u + gamma'`          |  +1.869140038399908983   |
  |   term `(2 alpha u - beta) u'`                  | +18.264149737206312849   |
  | two-point gap profile `gapLo`                   |  -1.0350216184e-05       |
  | two-point gap profile `gapHi`                   |  +1.0903606913e-05       |
  | gap sup bound `gapBound = 16 |gapHi| / (1-s_c^2)^6` | +1.7264239523e-03   |
  | `T'' (x_c)` bracket                             | 9.841042301830534 .. 9.841042301830535 |
  | `T'' (x_d)` bracket                             | 9.841042301830834 .. 9.841042301830834 |
  | rung bracket `4 (T'' x_c + T'' x_d + gap)`      | 78.7283384146455 .. 78.7283384149908 |
  | certified decimal bracket                       | [787283384/10^7, 787283385/10^7] |
  +------------------------------------------------+--------------------------+

  (The Lean certificate's final comparison is deliberately coarse: any
  rational point strictly between the two rung endpoints works, and
  `787283384/10^7 < 78.7283384146455` and `78.7283384149908 < 787283385/10^7`
  by `norm_num`.)

- Rig `scripts/seed_third_order_interval_certificate_1976.py` (independent
  exact-rational re-implementation of the same enclosure, used to choose the
  partition): the 22 + 15 piece partition has constant sign on every piece
  (worst left margin `-0.1395`, at `[27/50, 109/200]`; worst right margin
  `+6.530e-3`, at `[577/1000, 291/500]`), the straddle certificate is
  positive, and the rung bracket has width `3.45e-10` — i.e.
  the certificate's granularity, not the mathematics, is what the `1e-7`
  bracket reflects.

- The threshold coupling with record 1975: the crossing `s*` of this brick is
  the crossing of the comparison `u - thirdOrderThreshold s` from 1975 (the
  same `x* = 0.218255829186`); this record closes the "Still open" item of
  1975 verbatim, with the single deviation that the logistic enclosure is by
  the power form `(1 + y)^m` rather than `(1 + v/n)^n`.

## Still open

The rung's exact value remains the transcendental `8 * T'' x*`; what is
certified is a rational bracket, not a closed form. The brick certifies the
sign of `T'''` on two half-lines and in a gap, which is all that the rung
needs; it does not assert single-peakedness of `T''` (that remains equivalent
to the crossing statement, now certified numerically to `1e-7`). Nothing here
touches the higher rungs `j >= 4`, the transition bound, or the committed
consumer chain of the explicit-seed budget, and nothing here asserts RH.