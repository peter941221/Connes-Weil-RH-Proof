# Record 1968: Explicit derivative constant for the committed smooth seed

Date: 2026-09-25

## Closed

1. Exact derivative of the transition function. With

       u = expNegInvGlue x,  v = expNegInvGlue (1 - x),  a = x^-1,  b = (1 - x)^-1

   Lean proves, for every real x, the closed form

       deriv Real.smoothTransition x
         = ((x^-1)^2 * u * v + u * ((1 - x)^-1)^2 * v) / (u + v)^2

   together with the corresponding HasDerivAt statement.

2. Sharp constant for the transition function:

       norm (deriv Real.smoothTransition x) <= 2

   for every real x, and 2 is attained at x = 1/2: there a = b = 2 and
   u = v = exp(-2), so the closed form returns 8 exp(-4) / (4 exp(-4)) = 2.
   The proof reduces to the one-variable inequality

       2 + 4 cosh t + 2 cosh (2t) <= 8 cosh (sinh t)^2

   for every real t, which follows from cosh (2t) <= cosh (2 sinh t)
   (via self_le_sinh_iff) and 1 <= cosh t. The reduction uses the identity
   (a - 1) (b - 1) = 1 for a = x^-1, b = (1 - x)^-1 on 0 < x < 1, with the
   two constant branches of the transition function on the remaining ranges.

3. Pointwise bound for the committed seed. With

       smoothSeedRaw x = smoothTransition (x + 2) * smoothTransition (2 - x)

   Lean proves, for every real x,

       norm (deriv smoothSeedRaw x) <= 4

   Both factors are bounded in modulus by 1, so the product rule gives
   2 * 1 + 1 * 2 = 4. This constant is not sharp: the two derivative factors
   are supported in (-2,-1) and (1,2) respectively, where the other factor
   equals 1 and has zero derivative, so the true supremum is 2 (attained at
   x = +-3/2). The product form is what the current budget chain consumes.

4. Complex and CompactLogTest packaging. Lean proves

       norm (deriv smoothSeedComplex x) <= 4

   and the same bound for the actual test function of the committed
   CompactLogTest seed:

       norm (deriv (smoothSeed.test : R -> C) x) <= 4

   The second is read off the coercion identity smoothSeed.test x =
   smoothSeedComplex x, which is rfl in the committed seed.

5. The derivative keeps the seed support:

       support (deriv (smoothSeed.test : R -> C)) <= Icc (-2) 2

   since the seed is eventually zero at both ends (eventual-equality plus
   deriv_eq).

6. The budget consumer closes. With B = 2 and M = 4 the committed
   derivativeL1_le_of_support_of_norm_le returns

       derivativeL1 smoothSeed <= (2 * 2) * 4 = 16

   This closes the named obligation of record 1967 (the direct product
   derivative bound for smoothSeedRaw).

## Evidence

- Module: ConnesWeilRH/Dev/C1ExplicitSmoothSeedDerivativeValue.lean
- Audit: ConnesWeilRH/Dev/C1ExplicitSmoothSeedDerivativeValueAudit.lean
- Build: lake build ConnesWeilRH.Dev.C1ExplicitSmoothSeedDerivativeValue
  ConnesWeilRH.Dev.C1ExplicitSmoothSeedDerivativeValueAudit
- Build completed successfully (3645 jobs); zero error lines, zero sorryAx,
  no warnings in the two new modules.
- All 14 audited declarations use only propext, Classical.choice, and
  Quot.sound.

## Still open

- The constant 16 is an upper bound. The sharp seed derivative bound (2) and
  hence the sharp budget 8 are not formalized; the region split that gives
  them is the named sharpening.
- No constants are chosen here for the shifted-product recurrence, the node
  product, or the strip contraction.
- The numerical cardinalRaw budget at any concrete node set, the correction
  quadratic margin, the signed determinant, and the joint tail margin stay
  open. Therefore RH remains unproved.