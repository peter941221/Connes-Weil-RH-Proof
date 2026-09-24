# Record 1969: Sharp derivative constant for the committed smooth seed

Date: 2026-09-25

## Closed

1. The transition derivative vanishes where the transition function is
   constant. For every real y with `1 <= y`,

       deriv Real.smoothTransition y = 0

   (`deriv_smoothTransition_eq_zero_of_one_le`). The proof substitutes
   `expNegInvGlue (1 - y) = 0` into the closed form of record 1968, which
   kills both numerator terms, and the divisor is harmless.

2. Sharp pointwise bound for the committed seed:

       norm (deriv smoothSeedRaw x) <= 2

   for every real x (`norm_deriv_smoothSeedRaw_le_two`). The product rule of
   record 1968 writes the derivative as

       T' (x + 2) * T (2 - x) - T (x + 2) * T' (2 - x)

   and the two derivative factors never act at the same point:

       x <= 1  =>  2 - x >= 1  =>  T' (2 - x) = 0
                                 =>  derivative = T' (x + 2) * T (2 - x)
       1 <= x  =>  x + 2 >= 1  =>  T' (x + 2) = 0
                                 =>  derivative = - T (x + 2) * T' (2 - x)

   Since `0 <= T <= 1` and `norm (deriv T) <= 2`, both regions give `2`.

3. The bound is attained, so the constant is the exact supremum:

       deriv Real.smoothTransition (1/2) = 2
       deriv smoothSeedRaw (-3 / 2) = 2
       deriv smoothSeedRaw (3 / 2) = -2
       norm (deriv smoothSeedRaw (-3 / 2)) = 2

   At `x = 1/2` the closed form is `8 exp(-4) / (4 exp(-4)) = 2`
   (`deriv_smoothTransition_half`), which is the equality case of the
   transition bound; at `x = -3/2` the seed derivative equals
   `T' (1/2) * T (7/2)` and `T (7/2) = 1` with `T' (7/2) = 0`; at `x = 3/2`
   the two roles swap and the value is `-2`.

4. Complex and `CompactLogTest` packaging carry the same constant:

       norm (deriv smoothSeedComplex x) <= 2
       norm (deriv (smoothSeed.test : R -> C) x) <= 2

   via the coercion identity of the committed seed.

5. The budget consumer returns the halved constant:

       derivativeL1 smoothSeed <= (2 * 2) * 2 = 8

   by `derivativeL1_le_of_support_of_norm_le` with support radius `2` and
   sup `2`, sharpening record 1968's `16`.

6. The coarser statements of record 1968 (`<= 4`, `<= 16`) are left in place.
   They remain true, and nothing downstream consumes them as optimal.

## Evidence

- Module: ConnesWeilRH/Dev/C1ExplicitSmoothSeedDerivativeSharp.lean
- Audit: ConnesWeilRH/Dev/C1ExplicitSmoothSeedDerivativeSharpAudit.lean
- Build: lake build ConnesWeilRH.Dev.C1ExplicitSmoothSeedDerivativeSharp
  ConnesWeilRH.Dev.C1ExplicitSmoothSeedDerivativeSharpAudit
- Build completed successfully (3646 jobs); zero error lines, zero sorryAx,
  no warnings in the two new modules.
- All 9 audited declarations use only propext, Classical.choice, and
  Quot.sound.

## Still open

- The shifted-product recurrence constants and the node-product constants,
  which multiply this base, are not chosen here.
- The strip contraction is untouched.
- The numerical cardinalRaw budget at any concrete node set, the correction
  quadratic margin, the signed determinant, and the joint tail margin stay
  open. Therefore RH remains unproved.