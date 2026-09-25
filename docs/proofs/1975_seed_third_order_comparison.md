# Record 1975: The sign of `T'''` on the left half is one explicit comparison

Date: 2026-09-25

## Closed

1. The reduction. In the half-width coordinate

       s = 1 - 2 x,      x = (1 - s) / 2,      s in (0, 1),

   which covers exactly the left half `x in (0, 1/2)`, the committed
   third-order closed form of record 1974 rewrites as

       (1 - s^2)^6 * T''' ((1 - s) / 2)
         = 64 * (T x * (1 - T x)) * thirdOrderBracket s (1 - 2 T x)

   (`iteratedDeriv_three_smoothTransition_eq_bracket`), where
   `thirdOrderBracket` is the quadratic

       thirdOrderBracket s u = 4 (3 u^2 - 1) (1 + s^2)^3
         - 12 u s (1 + s^2) (3 + s^2) (1 - s^2)
         + 3 (1 + 6 s^2 + s^4) (1 - s^2)^2
         = thirdOrderLeading s * u^2 - thirdOrderMiddle s * u
           + thirdOrderConstant s

   (`thirdOrderBracket_eq_quadratic`). Since `T x * (1 - T x) > 0` on the open
   window and `(1 - s^2)^6 > 0`, the SIGN of `T'''` on the left half is the
   sign of the bracket, and the bracket is a quadratic in the single logistic
   variable `u = 1 - 2 T x`.

2. The bracket coefficients. Writing `s^2 = w`,

       thirdOrderLeading  s = 12 (1 + s^2)^3                        > 0,
       thirdOrderMiddle   s = 12 s (1 + s^2) (3 + s^2) (1 - s^2)    >= 0  on [0, 1],
       thirdOrderConstant s = 3 (1 + 6 s^2 + s^4) (1 - s^2)^2 - 4 (1 + s^2)^3
                            = -1 + s^4 (3 s^4 + 8 s^2 - 42)         < 0  on [0, 1]

   (`thirdOrderLeading_pos`, `thirdOrderMiddle_nonneg`, the identity and the
   bound `thirdOrderConstant_neg`). The constant term is negative because on
   `[0, 1]` the inner bracket is at most `3 + 8 - 42 = -31`, so the whole
   coefficient is at most `-1`: the two roots of the bracket sit on opposite
   sides of `0`, and for `u > 0` the sign is the sign of `u` minus the
   POSITIVE root. Sign-definiteness of the constant coefficient is the entire
   arithmetic input; no sign of the middle coefficient is needed.

3. The clearing identity. The three bracket terms of the closed form are
   homogeneous of degree `6, 6, 6` in the pair `(1 + s^2, 1 - s^2)` after
   multiplication by `(1 - s^2)^6`:

       (1 - s^2)^6 * ( ((3 u^2 - 1) / 2) * (8 (1 + s^2) / (1 - s^2)^2)^3
                       + 3 u * (8 (1 + s^2) / (1 - s^2)^2)
                           * (-(32 s (3 + s^2) / (1 - s^2)^3))
                       + 192 (1 + 6 s^2 + s^4) / (1 - s^2)^4 )
         = 64 * thirdOrderBracket s u

   (`bracket_clearing`, proved by `field_simp` on the four explicit nonzero
   powers followed by `ring`). The degree-two first factor of the closed form
   is normalized in the same variable by
   `(1 - 2 t)^2 - 2 t (1 - t) = (3 (1 - 2 t)^2 - 1) / 2`
   (`logistic_degree_two_normal_form`) -- prose only in record 1974, a
   committed identity now.

4. The two sign rules. For `a > 0 > c` and `u > 0` the quadratic
   `P u = a u^2 - b u + c` satisfies

       0 < P u  <->  (b + sqrt (b^2 - 4 a c)) / (2 a) < u,
       P u < 0  <->  u < (b + sqrt (b^2 - 4 a c)) / (2 a)

   (`quadratic_pos_iff`, `quadratic_neg_iff`). Both proofs rest on the
   discriminant identity
   `4 a P u = (2 a u - b)^2 - (b^2 - 4 a c)`
   (`quadratic_discriminant_identity`), which removes every division from the
   squaring step: the comparison `u < root` is transported to
   `2 a u < b + sqrt D` by `lt_div_iff₀`, then split on the sign of `2 a u - b`
   and squared only there. The `c < 0` hypothesis is used exactly once, at the
   disagreement case `2 a u < b`, where `P u < u (a u - b) < 0` directly. The
   sign transfer through a positive factor is the local lemma
   `mul_neg_of_pos_left_iff` (the pinned Mathlib has `mul_pos_iff_of_pos_left`
   but no negative counterpart).

5. The threshold and the sign theorems. With

       thirdOrderThreshold s = (thirdOrderMiddle s
         + sqrt (thirdOrderMiddle s^2
             - 4 * thirdOrderLeading s * thirdOrderConstant s))
         / (2 * thirdOrderLeading s)

   (`thirdOrderThreshold`, positive on `[0, 1]` by
   `thirdOrderThreshold_pos`), the two main theorems read

       0 < T''' ((1 - s) / 2)          <->  thirdOrderThreshold s < 1 - 2 T x,
       T''' ((1 - s) / 2) < 0          <->  1 - 2 T x < thirdOrderThreshold s

   (`iteratedDeriv_three_smoothTransition_sign_iff`,
   `iteratedDeriv_three_smoothTransition_neg_iff`). The logistic input
   `0 < 1 - 2 T x` is the committed reflection route: the evaluation at
   `(1 + s) / 2` transported by `windowGain_one_sub` and companions, the
   logistic pair `(e^v - 1) / (e^v + 1)` at `v = 4 s / (1 - s^2)` from
   `one_sub_two_mul_smoothTransition_eq` and `reflectPoint_one_sub_two_div`
   (`one_sub_two_mul_smoothTransition_reflect_eq`), and its positivity
   (`one_sub_two_mul_smoothTransition_reflect_pos`). The one evaluation not
   previously committed is the second gain slope at the standard point,
   `windowGainSecondSlope ((1 + s) / 2) = 192 (1 + 6 s^2 + s^4) / (1 - s^2)^4`
   (`windowGainSecondSlope_standard_eq`; record 1974 pinned `G''` only at
   `1 / 2`), from which `windowGainSecondSlope_reflect_eq` follows by
   reflection.

6. What this buys. Single-peakedness of `T''` on `(0, 1/2)` is now EXACTLY the
   statement that the one-variable comparison

       1 - 2 T x   against   thirdOrderThreshold (1 - 2 x)

   crosses once on `s in (0, 1)`, i.e. that `tanh (v/2)` crosses the quadratic
   irrationality `(beta + sqrt (beta^2 - 4 alpha gamma)) / (2 alpha)` once,
   with `alpha, beta, gamma` the explicit polynomials of item 2. No
   differentiability, no cancellation, and no further algebra is left between
   this comparison and the uniqueness of the interior zero `x*`.

## Evidence

- Modules: `ConnesWeilRH/Dev/C1ExplicitSeedThirdOrderComparison.lean` and its
  paired `...Audit.lean`; build log
  `build-logs/1975_seed_third_order_comparison.log`, footer
  `Build completed successfully (3653 jobs)`, zero `error:` lines, zero
  `sorryAx`, no warnings in the two new modules; all 25 audited declarations
  depend on exactly `[propext, Classical.choice, Quot.sound]`.
- Rig: `scripts/seed_single_peakedness_probe_1975.py`, log
  `build-logs/1975_single_peakedness_probe.log`. Checks: the factored identity
  against the committed closed form has worst relative residual `4.15e-08`
  (at `s = 0.95`, where both sides are of order `4e-08`: the absolute
  difference is at the `1e-16` model floor); `P(0, 0) = -1` exactly, and
  `16 P / (1 - s^2)^6` at `s = 0` equals `-16` exactly, the committed
  `T'''(1/2)`; the polynomial identity for `gamma` is checked in exact
  `Fraction` arithmetic at `w = 1/4, 1/9, 1/2, 4/25` (`-893/256`,
  `-3296/2187`, `-165/16`, `-797057/390625`, all equal); the discriminants are
  exact rationals, `Delta (1/2) = 169275/256`, `Delta (1) = 12288`.
- The crossing: `s* = 0.563488341628`, i.e. `x* = 0.218255829186`, the same
  interior zero record 1974 located (probe bisection, `T'''` factored value
  `-2.5e-13` there); the crossing value is
  `u (s*) = thirdOrderThreshold (s*) = 0.929034992747`, and `T'' (x*) =
  9.841042301831` reproduces the 1974 reading. Margins of the comparison
  `u - threshold` on the grid: most negative `-0.2887` on the left (at
  `s -> 0`), and on the right `+1.07e-03` just past the crossing
  (`+0.00697` at `s = 0.57`, `+0.4126` at `s = 0.99`); the range of the
  threshold on `(0, 1)` is `[0.290179, 0.938579]`.
- The logical bridge to item 1: `u > 0` on the left half is
  `one_sub_two_mul_smoothTransition_reflect_pos`, and
  `a > 0 > c` on `[0, 1]` is `thirdOrderLeading_pos` with
  `thirdOrderConstant_neg`, so both sign rules apply verbatim with
  `(a, b, c) = (thirdOrderLeading, thirdOrderMiddle, thirdOrderConstant)`.

## Still open

The interval certificate for the single crossing of item 6: a finite
partition of `(0, 1)` on which the comparison has a constant sign, with the
logistic side enclosed by rational bounds on `Real.exp` (for instance
`(1 + v/n)^n <= e^v <= (1 - v/n)^{-n}`) and the threshold side by rational
bounds on the square root. The margins show this is feasible away from `s*`
and delicate only in a narrow window just past `s*`, where the comparison is
positive but small (`1.07e-03` on the grid). That certificate is exactly what
turns the implicit expression `8 * T'' x*` for the third rung into a
certified rational bracket `8 * T''` on either side of `x*`, and supplies the
upper bound matching the committed
`4 * T'' x <= derivOrderL1 3 smoothSeed`. A rational bracket on `x*` itself
then follows from the monotonicity of `u` in `s` on the same partition.

Nothing in this record asserts single-peakedness: what is proved is that the
single-peakedness of `T''` on `(0, 1/2)` and the one crossing of a logistic
curve with an explicit quadratic irrationality are the same proposition.
Therefore RH remains unproved.
