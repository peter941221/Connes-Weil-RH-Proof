# Record 1973: The second rung of the seed ladder is exactly eight

Date: 2026-09-25

## Closed

1. The committed closed form of the transition derivative factors through the
   logistic pair and the gain. With `T = Real.smoothTransition` and

       windowGain x = (x^-1)^2 + ((1 - x)^-1)^2

   the committed formula `deriv T x = ((x^-1)^2 * u * v + u * ((1-x)^-1)^2 *
   v) / (u + v)^2` rewrites to

       deriv T x = T x * (1 - T x) * windowGain x

   (`deriv_smoothTransition_eq_mul_windowGain`). The identity is universal in
   `x`: unfolding `Real.smoothTransition` and `windowGain` sends both sides to
   `0` outside the window through the `inv_zero` conventions, so no case split
   is needed. The gain is even under the reflection `x -> 1 - x`
   (`windowGain_one_sub`) and its derivative, named

       windowGainSlope x = -2 * (x^-1)^3 + 2 * ((1 - x)^-1)^3,

   is odd under it (`windowGainSlope_one_sub`) and is computed by the chain
   rule from `hasDerivAt_inv` alone (`hasDerivAt_windowGain`; the derivative
   value of `(y^-1)^2` carries the exponent `2 - 1`, which the proof reduces
   with `show (2 : Nat) - 1 = 1`, `pow_one`, and `inv_pow`).

2. On the open window the pair `1 - 2 T` is the logistic ratio in the
   exponential variable `w = (1 - 2 x) / (x * (1 - x))`:

       1 - 2 T x = (exp w - 1) / (exp w + 1)

   (`one_sub_two_mul_smoothTransition_eq`, from
   `expNegInvGlue (1 - x) = exp w * expNegInvGlue x`, itself the addition
   formula for `exp` with the exponent identity
   `-1/(1-x) + 1/x = (1-2x)/(x(1-x))`). Reflecting the variable gives
   `(exp (-w) - 1)/(exp (-w) + 1) = -((exp w - 1)/(exp w + 1))`
   (`exp_neg_sub_one_div_exp_neg_add_one`), and the logistic ratio is bounded
   below by the elementary convexity inequality `1 + v <= exp v`:

       v / (v + 2) <= (exp v - 1) / (exp v + 1)   for v >= 0

   (`self_div_add_two_le_exp_ratio`; the equivalence is exactly
   `v <= v * exp v + 2 * exp v - 2`, i.e. `0 <= 2 * (exp v - v - 1)`). No
   hyperbolic estimate is needed anywhere.

3. The polynomial comparison. Substituting the standard point `x = (1 + s)/2`
   (equivalently `s = |2x - 1|`) gives

       windowGain ((1 + s)/2) = 8 * (1 + s^2) / (1 - s^2)^2
       windowGainSlope ((1 + s)/2) = 32 * s * (s^2 + 3) / (1 - s^2)^3

   (`windowGain_half_eq`, `windowGainSlope_half_eq`) and therefore the gain
   ratio identity

       windowGainSlope ((1 + s)/2)
         = (s (s^2 + 3) (1 - s^2) / (2 (1 + s^2)^2)) * windowGain ((1+s)/2)^2

   (`windowGainSlope_div_sq_half_eq`). At the logistic variable
   `v = 4 s / (1 - s^2)` the ratio is strictly dominated:

       s (s^2 + 3) (1 - s^2) / (2 (1 + s^2)^2) < (exp v - 1)/(exp v + 1)

   (`windowGain_ratio_lt_exp_ratio`). The polynomial core is
   `2 s / (1 + 2 s - s^2)` versus the gain ratio, and the comparison reduces to

       4 (1 + s^2)^2 - (s^2 + 3) (1 - s^2) (1 + 2 s - s^2)
         = (13 s^2 - 6 s + 1) + s^3 (4 + 3 s + 2 s^2 - s^3) > 0   on [0, 1],

   where `13 s^2 - 6 s + 1 = ((13 s - 3)^2 + 4)/13 > 0` and the second summand
   is nonnegative for `s <= 1`; the logistic variable at the standard point is
   `-v` (`halfPoint_one_sub_two_div`) and at the reflected point `+v`
   (`reflectPoint_one_sub_two_div`).

4. The second derivative in the gain form. Differentiating the factorization
   of item 1 by the product rule gives, on `(0, 1)`,

       T'' x = T x * (1 - T x) * ((1 - 2 T x) * windowGain x ^ 2
                                   + windowGainSlope x)

   (`iteratedDeriv_two_smoothTransition_eq`, with the bridge
   `iteratedDeriv 2 T = deriv (deriv T)` and `Pi.mul_apply` to reduce the
   applied product of functions). At the three special points the value
   vanishes by Fermat's theorem, with no differentiability input beyond what
   `IsLocalMin.deriv_eq_zero` and `IsLocalMax.deriv_eq_zero` absorb:

       T'' 0 = 0,     T'' 1 = 0,     T'' (1/2) = 0

   (`iteratedDeriv_two_smoothTransition_zero`, `..._one`, `..._half`), from the
   committed facts `0 <= deriv T` (minima at `0` and at `1`) and
   `deriv T (1/2) = 2` with `norm (deriv T x) <= 2` (maximum at `1/2`).

5. Sign of the second derivative. Using item 2 on each half with
   `s = 1 - 2 x` (left, reflected point) and `s = 2 x - 1` (right, standard
   point) and item 3 for the domination,

       0 <= T'' x   on (0, 1/2],         T'' x <= 0   on [1/2, 1)

   (`iteratedDeriv_two_smoothTransition_nonneg`,
   `..._nonpos`; the boundary `x = 1/2` in both lemmas is decided by the
   Fermat value of item 4). The second derivative has the sign of `1 - 2 x`:
   the logistic factor beats the geometric gain ratio.

6. The absolute-value mass. The transition rises from `0` to `1` and flattens
   out at `1`, so the fundamental theorem of calculus on the two halves gives

       Integral x in 0..1/2, T'' x = T' (1/2) - T' 0 = 2
       Integral x in 1/2..1, T'' x = T' 1 - T' (1/2) = -2

   (`integral_iteratedDeriv_two_smoothTransition_left`, `..._right`; the
   endpoint values come from the Fermat lemmas, and `ContDiffOn` at order `1`
   is the committed `contDiff_one_iteratedDeriv_smoothTransition 1`). The sign
   of item 5 converts the absolute value into the function on the left half
   and into its negative on the right half
   (`integral_abs_iteratedDeriv_two_smoothTransition_left`, `..._right`), and
   the absolute-value mass is the exact number

       Integral x, norm (T'' x) = 4

   (`integral_abs_iteratedDeriv_two_smoothTransition`), by splitting the
   compactly supported integral at `1/2` and adding `2 + 2`. With the ladder
   identity of record 1972 the second rung is

       derivOrderL1 2 smoothSeed = 8

   (`derivOrderL1_smoothSeed_two`). The committed oracle bound at order two
   remains `2 * sup norm (T'')`; the value itself is now a number.

The order-`j` values for `j >= 3` remain the single integral
`2 * Integral x, norm (iteratedDeriv j T x)`; no number is claimed for them.

## Evidence

- Module: ConnesWeilRH/Dev/C1ExplicitSeedSecondOrderMass.lean
- Audit: ConnesWeilRH/Dev/C1ExplicitSeedSecondOrderMassAudit.lean
- Build: lake build ConnesWeilRH.Dev.C1ExplicitSeedSecondOrderMass
  ConnesWeilRH.Dev.C1ExplicitSeedSecondOrderMassAudit
- Build completed successfully (3651 jobs); zero error lines, zero sorryAx,
  no warnings in the two new modules.
- All 27 audited declarations use only propext, Classical.choice, and
  Quot.sound.

## Still open

- The third rung `derivOrderL1 3 smoothSeed` needs the sign structure of
  `T'''`: the second-derivative argument above uses convexity of `exp` and a
  degree-2 polynomial comparison, and the next order has no such reduction
  yet.
- The node-product constants, the strip contraction, the numerical cardinalRaw
  budget at a concrete node set, the correction quadratic margin, the signed
  determinant, and the joint tail margin stay open. `C > 0` still has to come
  from a designed admissible base on the construction side. Therefore RH
  remains unproved.