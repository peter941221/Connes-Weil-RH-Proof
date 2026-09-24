# Record 1971: Support stability under differentiation — one radius for the whole ladder

Date: 2026-09-25

## Closed

1. The support of a derivative stays in the closure of the support of the
   function:

       support (deriv f) ⊆ closure (support f)

   for every `f : ℝ → ℂ` (`support_deriv_subset_closure_support`). A point
   outside the closure has an open neighbourhood on which the function
   vanishes identically, so the function is eventually `0` there and the
   derivative vanishes at the point by `Filter.EventuallyEq.deriv_eq` and
   `deriv_const`. No differentiability hypothesis is needed, since `deriv` is
   already `0` where the function is eventually `0`.

2. Iterating gives the same for every iterated derivative
   (`support_iteratedDeriv_subset_closure_support`, by induction on the order
   using `iteratedDeriv_succ` and `closure_mono`, `closure_closure`), and hence
   a single closed interval bounds every order: the support hypothesis is
   needed at the function only (`support_iteratedDeriv_subset_Icc`, through
   `closure_minimal` and `isClosed_Icc`).

3. The committed seed carries that hypothesis at the function level:
   `support (smoothSeed.test) ⊆ [-2, 2]` (`support_smoothSeed_test_subset`,
   the function-level companion of the committed derivative-level
   `support_deriv_smoothSeed_test_subset`). Therefore every iterated
   derivative of the committed seed has support in `[-2, 2]`, and the radius
   of the ladder budget is one number for all orders.

4. The order-`m` budget with the radius taken at the function:

       derivOrderL1 m f <= (2 * B) * M

   whenever `support (f.test) ⊆ [-B, B]` and `M` bounds the `m`-th derivative
   (`derivOrderL1_le_of_supportRadius`). This is the order-`m`
   support-times-sup budget of record 1970 with its support slot discharged
   once and for all orders.

5. The seed oracle: for every order `m` and every real `M` bounding the
   `m`-th derivative of the committed seed,

       derivOrderL1 m smoothSeed <= 4 * M

   (`derivOrderL1_smoothSeed_le`), the factor `4` being `2 * B` at the fixed
   radius `B = 2`. The `m = 1` case with the committed sup bound `2` returns
   `derivativeL1 smoothSeed <= 8` (`derivOrderL1_one_smoothSeed_le_eight`),
   which is record 1969's committed constant obtained through the new route:
   a consistency check, not a new number.

6. The ladder budget is monotone in the ladder
   (`ladderBound_mono`, by induction on the node list with the order
   generalized), so the seed-level statement needs one unknown family only:
   whenever `M j` bounds the `j`-th derivative of the committed seed for every
   `j`,

       l1Mass (shiftedProduct nodes smoothSeed) <= ladderBound (4 * M ·) nodes 0

   (`l1Mass_shiftedProduct_smoothSeed_le`).

7. The ladder reaches the committed owner functional. The committed consumer
   `l1Mass_cardinalRaw_le_of_budget` accepts the ladder of the exponentially
   weighted seed as its budget function — its step condition is exactly the
   ladder recursion — so for every node set, seed and base point

       l1Mass (cardinalRaw nodes f z)
         <= ladderBound (derivOrderL1 · (exponentialWeight f (-z)))
             (nodes.erase z).toList 0

   (`l1Mass_cardinalRaw_le_ladder`).

So the shifted-product budget for the committed seed is now a bound with the
radius fixed and exactly one unknown family per order: the sup norms of the
seed's iterated derivatives. Nothing else is missing at this step, and no
number is chosen for that family here.

## Evidence

- Module: ConnesWeilRH/Dev/C1ExplicitDerivativeSupportStability.lean
- Audit: ConnesWeilRH/Dev/C1ExplicitDerivativeSupportStabilityAudit.lean
- Build: lake build ConnesWeilRH.Dev.C1ExplicitDerivativeSupportStability
  ConnesWeilRH.Dev.C1ExplicitDerivativeSupportStabilityAudit
- Build completed successfully (3648 jobs); zero error lines, zero sorryAx,
  no warnings in the two new modules.
- All 10 audited declarations use only propext, Classical.choice, and
  Quot.sound.

## Still open

- No number is chosen for the family `M` of sup norms of the seed's iterated
  derivatives; the ladder is a bound with one unknown family, not a numeric
  budget.
- The node-product constants, the strip contraction, the numerical
  cardinalRaw budget at a concrete node set, the correction quadratic
  margin, the signed determinant, and the joint tail margin stay open.
  Therefore RH remains unproved.