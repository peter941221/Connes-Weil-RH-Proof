# Record 1972: The seed ladder over the transition function — one function, and the value at order one

Date: 2026-09-25

## Closed

1. The committed seed is a product of two translates of the transition
   function `T = Real.smoothTransition`, and each translate is constant on the
   side of the window where the other one acts: `T (x + 2)` equals `1` for
   `x >= -1`, and `T (2 - x)` equals `1` for `x <= 1`. So for every positive
   order only one term of the Leibniz sum is alive at a time:

       iteratedDeriv j smoothSeedRaw x
         = iteratedDeriv j T (x + 2) + (-1)^j * iteratedDeriv j T (2 - x)

   for `j >= 1` (`iteratedDeriv_smoothSeedRaw_eq`). On `x >= 1` the seed is
   eventually the reflected translate and on `x < 1` eventually the shifted
   one; both cases are `Filter.EventuallyEq.iteratedDeriv_eq` with the
   vanishing lemmas of item 2.

2. The transition derivatives vanish at both ends of the window:
   `iteratedDeriv j T` is `0` on `(-inf, 0]` for every order
   (`iteratedDeriv_smoothTransition_eq_zero_of_lt_zero`) and on `(1, inf)` for
   every positive order (`iteratedDeriv_smoothTransition_eq_zero_of_one_lt`;
   the positive-order hypothesis is genuine, the constant-one region fails at
   order zero). Hence `support (iteratedDeriv j T) <= [0, 1]` for `j >= 1`
   (`support_iteratedDeriv_smoothTransition_subset`), at every point at most
   one of the two terms of item 1 is nonzero, and the norms add:

       norm (iteratedDeriv j smoothSeedRaw x)
         = norm (iteratedDeriv j T (x + 2)) + norm (iteratedDeriv j T (2 - x))

   (`norm_iteratedDeriv_smoothSeedRaw_eq`), and the same at the committed
   complex packaging (`norm_iteratedDeriv_smoothSeed_test_eq`, through the
   coercion lemma `iteratedDeriv_smoothSeedComplex_eq`, whose induction needs
   only the `C^1` facts `contDiff_one_iteratedDeriv_smoothTransition`,
   `contDiff_one_iteratedDeriv_smoothSeedRaw` and
   `deriv_ofReal_comp_of_differentiableAt`).

3. Integrating that identity against Lebesgue measure, which is invariant
   under both the shift by `2` and the reflection, gives the ladder identity:
   for every `j >= 1`

       derivOrderL1 j smoothSeed = 2 * Integral x, norm (iteratedDeriv j T x)

   (`derivOrderL1_smoothSeed_eq`; the two pieces are integrable by compact
   support, `integrable_norm_iteratedDeriv_smoothTransition_add` and
   `..._sub`). The whole ladder of the committed seed is therefore the
   transition function's derivative mass doubled — one function, one integral
   per order, instead of a growing Leibniz expansion.

4. Order one is computable. The transition is nondecreasing from `0` to `1`,
   so its derivative is nonnegative (`deriv_smoothTransition_nonneg`, read off
   the committed closed form), supported in `[0, 1]`
   (`support_deriv_smoothTransition_subset`), and

       Integral x, norm (deriv T x) = 1

   (`integral_norm_deriv_smoothTransition_eq_one`, by the fundamental theorem
   of the interval integral on `[0, 1]`, where `T 1 - T 0 = 1`). With the
   ladder identity at `j = 1` this is the exact value

       derivativeL1 smoothSeed = 2

   (`derivativeL1_smoothSeed_eq_two`). The committed bound
   `derivativeL1 smoothSeed <= 8` of record 1969 is therefore not sharp: the
   first rung of the ladder is the number `2`.

5. The seed oracle needs the sup norms of one function only: for `j >= 1` and
   every real `M` bounding `norm (iteratedDeriv j T)`,

       derivOrderL1 j smoothSeed <= 2 * M

   (`derivOrderL1_smoothSeed_le_two_mul`). This is record 1971's factor `4`
   sharpened to `2`, with the transition's sup norms in place of the seed's.

6. The first numerically bounded rung of the seed ladder: for every node `a`,

       l1Mass (shiftedProduct [a] smoothSeed) <= 2 + 4 * norm a

   (`l1Mass_shiftedProduct_singleton_smoothSeed_le`), the ladder of record
   1970 at one node with items 3 and 4 as its two inputs and the committed
   `l1Mass smoothSeed <= 4` for the seed itself.

The order-`j` values for `j >= 2` remain the single integral
`2 * Integral x, norm (iteratedDeriv j T x)`; no number is claimed for them.

## Evidence

- Module: ConnesWeilRH/Dev/C1ExplicitSeedTransitionReduction.lean
- Audit: ConnesWeilRH/Dev/C1ExplicitSeedTransitionReductionAudit.lean
- Build: lake build ConnesWeilRH.Dev.C1ExplicitSeedTransitionReduction
  ConnesWeilRH.Dev.C1ExplicitSeedTransitionReductionAudit
- Build completed successfully (3650 jobs); zero error lines, zero sorryAx,
  no warnings in the two new modules.
- All 20 audited declarations use only propext, Classical.choice, and
  Quot.sound.

## Still open

- No number is chosen for the sup norms at order `j >= 2`; there the ladder is
  the explicit one-dimensional integral `2 * Integral x, norm (iteratedDeriv j
  T x)`, not a closed form.
- The node-product constants, the strip contraction, the numerical cardinalRaw
  budget at a concrete node set, the correction quadratic margin, the signed
  determinant, and the joint tail margin stay open. Therefore RH remains
  unproved.