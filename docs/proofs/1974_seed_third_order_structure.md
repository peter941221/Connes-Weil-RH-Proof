# Record 1974: The third rung of the seed ladder is not a number

Date: 2026-09-25

## Closed

1. The second slope of the gain. With

       windowGainSlope x = -2 * (x^-1)^3 + 2 * ((1 - x)^-1)^3

   the committed slope, the chain rule on `hasDerivAt_inv` alone gives

       windowGainSecondSlope x = 6 * (x^-1)^4 + 6 * ((1 - x)^-1)^4

   (`windowGainSecondSlope`, `hasDerivAt_windowGainSlope`). The new brick is
   even under the reflection (`windowGainSecondSlope_one_sub`), strictly
   positive on the open window (`windowGainSecondSlope_pos`), and takes the
   value `192` at the midpoint (`windowGainSecondSlope_half_eq`). In closed
   form this is the second derivative of the gain, `G'' x = 6 x^-4 + 6
   (1 - x)^-4`.

2. The reflection identity of the transition. Unfolding the committed
   definition in the exponential variable gives the exact identity

       smoothTransition (1 - x) = 1 - smoothTransition x

   (`smoothTransition_one_sub`; the proof needs both nonzero denominator facts
   `expNegInvGlue x + expNegInvGlue (1 - x)` and its reflection, cleared by
   `field_simp`). Consequently the logistic pair flips sign under reflection,

       1 - 2 * T (1 - x) = -(1 - 2 * T x)

   (`one_sub_two_mul_smoothTransition_one_sub`), the midpoint value is
   `T (1/2) = 1/2` (`smoothTransition_half_eq`), and at the midpoint the gain
   and its slope are the numbers `8` and `0`
   (`windowGain_half_point_eq`, `windowGainSlope_half_point_eq`), so that
   `T * (1 - T) = 1/4` there.

3. The third derivative in the gain form. Differentiating the committed
   second-order form by the product rule (bridge
   `iteratedDeriv 3 T = deriv (iteratedDeriv 2 T)`,
   `iteratedDeriv_three_smoothTransition_eq_deriv_deriv`) gives, on `(0, 1)`,

       T''' x = T x * (1 - T x) * ( ((1 - 2 T x)^2 - 2 T x (1 - T x))
                                     * windowGain x^3
                                   + 3 * (1 - 2 T x) * windowGain x
                                     * windowGainSlope x
                                   + windowGainSecondSlope x )

   (`hasDerivAt_iteratedDeriv_two_smoothTransition`,
   `iteratedDeriv_three_smoothTransition_eq`). The bracket coefficient is
   `3`, not `2`: the first hand pass used `2 * (1 - 2 T) * G * G'` and the
   probe rejects it by a Richardson central difference of `T''` at `x = 0.218`
   (wrong form `135.868`, finite difference `0.367`). With `u = 1 - 2 T` the
   first bracket coefficient has the algebraic normal form

       (1 - 2 T)^2 - 2 T (1 - T) = (3 u^2 - 1) / 2,

   so after clearing the factor two the bracket is
   `(3 u^2 - 1) * G^3 + 6 u * G * G' + 2 * G''`: three terms of different
   homogeneity whose interior zero is a cancellation among all three, not the
   zero of the leading one (the leading term alone vanishes at
   `x = 0.350163715843`, the bracket at the point of item 7).

4. Reflection and the midpoint value of the second and third derivatives. On
   the open window the two closed forms transport through item 2 and the two
   gain reflection identities:

       T'' (1 - x) = -T'' x,          T''' (1 - x) = T''' x

   (`iteratedDeriv_two_smoothTransition_one_sub`,
   `iteratedDeriv_three_smoothTransition_one_sub`). At the midpoint the four
   point values reduce the closed form to a rational number:

       T''' (1/2) = -16

   (`iteratedDeriv_three_smoothTransition_half`).

5. Fermat's theorem at the endpoints. The committed sign lemmas of record
   1973 are upgraded to genuine local extrema through a one-sided
   neighbourhood:

       T'' has a local minimum at `0` and a local maximum at `1`

   (`isLocalMin_iteratedDeriv_two_smoothTransition`,
   `isLocalMax_iteratedDeriv_two_smoothTransition`; the witnesses are
   `Ioo_mem_nhds`, which only needs the open conditions `-1/2 < 0`, `0 < 1/2`
   and `1/2 < 1`, `1 < 3/2`). Fermat's theorem then gives the two endpoint
   values of the third derivative with no differentiability input beyond
   `IsLocalMin.deriv_eq_zero` and `IsLocalMax.deriv_eq_zero`:

       T''' 0 = 0,          T''' 1 = 0

   (`iteratedDeriv_three_smoothTransition_zero`,
   `iteratedDeriv_three_smoothTransition_one`).

6. The vanishing left-half integral. The fundamental theorem of calculus at
   order one (`intervalIntegral.integral_deriv_of_contDiffOn_Icc` with the
   committed `contDiff_one_iteratedDeriv_smoothTransition 2`) gives

       Integral x in 0..1/2, T''' x = T'' (1/2) - T'' 0 = 0

   (`integral_iteratedDeriv_three_smoothTransition_left`). This is the exact
   third-order analogue of the order-two boundary computation, and it is the
   last place where the third rung still behaves like a number.

7. The third rung is not a number. The bracket of item 3 vanishes inside the
   left half at the transcendental point

       x* = 0.218255829186...

   (the probe isolated the zero by bisection, `T'''` changing sign from
   `+0.1434` to `-0.1432` across it; at that point `T''` attains its peak
   `T'' x* = 9.841042301831`). The cancellation is genuine: at `x*` the three
   cleared terms of item 3 read `+1.841656e4`, `-2.373702e4`, `+5.320452e3`,
   summing to `2.8e-10`, with the leading coefficient `3 u^2 - 1 = 1.589`
   far from zero. Since `T''` still rises from `0` to this single
   peak and returns to `0` at `1/2`, the third derivative is positive exactly
   on `(0, x*)` and negative on `(x*, 1/2]`, and the total-variation identity
   on the left half reads

       Integral x in 0..1/2, norm (T''' x) = 2 * T'' x*,

   measured by the probe to a residual of `5e-9` at `19.6820845987` versus
   `2 * T'' x* = 19.6820846037`. By the reflection of item 4 the right half
   doubles the value, so the third rung of the seed ladder is the
   transcendental constant

       derivOrderL1 3 smoothSeed = 8 * T'' x* = 78.728338... ,

   measured by quadrature as `78.72833839` against `8 * T'' x* =
   78.72833841`. The order-two mechanism (Fermat signs, `+- 2`, mass `4`) has
   no third-order analogue: the sign flip is interior, not at an endpoint, and
   the value is a peak of the lower derivative, not an integer. No number is
   claimed: the identity above rests on the single-peakedness of `T''`, which
   is open.

8. The quantitative handle. Without single-peakedness the norm mass of `T'''`
   over the left half still absorbs every point value of `T''`:

       norm (T''' (1 - u)) = norm (T''' u)          for u in [0, 1/2]
       T'' x <= Integral y in 0..x, norm (T''' y)   for 0 < x < 1/2
       T'' x <= Integral y in 0..1/2, norm (T''' y)
       4 * T'' x <= derivOrderL1 3 smoothSeed      for 0 < x < 1/2

   (`norm_iteratedDeriv_three_one_sub`,
   `iteratedDeriv_two_le_integral_norm_iteratedDeriv_three`,
   `iteratedDeriv_two_le_integral_norm_iteratedDeriv_three_left`,
   `derivOrderL1_smoothSeed_three_ge`). The tool chain is the FTC comparison
   `norm (integral) <= integral (norm)` at order three, the reflection
   identity `intervalIntegral.integral_comp_sub_left` with the norm transport
   of the first line, and the support confinement of record 1972 to reduce the
   full-line integral to twice the half-line one. This is the certified
   half of the rung: one point value of `T''` certifies a lower bound, and the
   matching upper bound is exactly the open single-peakedness.

## Evidence

- Module: ConnesWeilRH/Dev/C1ExplicitSeedThirdOrderStructure.lean
- Audit: ConnesWeilRH/Dev/C1ExplicitSeedThirdOrderStructureAudit.lean
- Build: lake build ConnesWeilRH.Dev.C1ExplicitSeedThirdOrderStructure
  ConnesWeilRH.Dev.C1ExplicitSeedThirdOrderStructureAudit
- Build completed successfully (3652 jobs); zero error lines, zero sorryAx,
  no warnings in the two new modules.
- All 24 audited declarations use only propext, Classical.choice, and
  Quot.sound.
- Probe: scripts/seed_third_order_probe_1974.py (provenance string "record
  1974 third-order probe; formulas from records 1972/1973"). Numbers quoted
  above: closed form against Richardson differences worst relative residual
  `5.31e-07` (at `x = 0.05`, the small-value end), symmetry worst `1.94e-13`,
  interior zero `0.218255829186`, peak `9.841042301831`, quadrature at
  `n = 200000` giving `78.72833839`, identity residual `5e-9`, the bracket
  decomposition at `x*` (`+1.841656e4`, `-2.373702e4`, `+5.320452e3`), and
  the leading-term zero `0.350163715843`.

## Still open

- Single-peakedness of `T''` on `(0, 1/2)`, equivalently the certified value
  `8 * T'' x*` of the third rung. The order-two analogue was decided by a
  degree-four polynomial comparison; the third order needs the sign of the
  bracket `(3 u^2 - 1)/2 * G^3 + 3 u G G' + G''` away from the midpoint, which
  is a comparison between the logistic ratio and a degree-three rational
  function, not yet reduced to a polynomial.
- A certified two-sided bracket on `x*` (a rational enclosure of the
  transcendental zero) so the transcendental constant becomes a machine-checked
  interval.
- The node-product constants, the strip contraction, the numerical cardinalRaw
  budget at a concrete node set, the correction quadratic margin, the signed
  determinant, and the joint tail margin stay open. `C > 0` still has to come
  from a designed admissible base on the construction side. Therefore RH
  remains unproved.