# Record 1970: The derivative ladder for shifted products

Date: 2026-09-25

## Closed

1. The `L¹` mass of the `m`-th iterated derivative of a compact log test,

       derivOrderL1 m f = ∫ x, norm (iteratedDeriv m (f.test) x)

   is the ladder of the committed budgets: it starts at the mass and meets the
   committed derivative budget at order one,

       derivOrderL1 0 f = l1Mass f          (derivOrderL1_zero)
       derivOrderL1 1 f = derivativeL1 f    (derivOrderL1_one)

   and it is nonnegative at every order (`derivOrderL1_nonneg`).

2. Every ladder value is finite. The iterated derivative of a compact log
   test is smooth with compact support (`contDiff_iteratedDeriv`,
   `hasCompactSupport_iteratedDeriv`, by induction on the order using
   `HasCompactSupport.deriv`), hence its norm is integrable
   (`iteratedDeriv_integrable`). Each of the three facts is proved for every
   order and every compact log test.

3. One shift raises the order. For every order `m`, compact log test `f` and
   complex `a`,

       iteratedDeriv m ((derivativeShift f a).test) x
         = iteratedDeriv (m + 1) (f.test) x + a * iteratedDeriv m (f.test) x

   (`iteratedDeriv_derivativeShift_apply`), from the function identity
   `(derivativeShift f a).test = deriv f.test + a * f.test`, linearity of the
   iterated derivative in the second summand, and `iteratedDeriv_succ'` in the
   first. Integrating the pointwise norm bound gives the shifted-product step

       derivOrderL1 m (derivativeShift f a)
         <= derivOrderL1 (m + 1) f + norm a * derivOrderL1 m f

   (`derivOrderL1_derivativeShift_le`), which is the committed
   `l1Mass_derivativeShift_le` one order up.

   Order bookkeeping note: `ContDiff.iterate_deriv` produces the smooth order
   `∞`, which in `ℕ∞ω = WithTop ℕ∞` is the coercion `↑⊤`, strictly below the
   analytic top `⊤` (the order `ω`). The comparison needed to lower `∞` to a
   natural order is therefore `↑m <= ↑⊤`, supplied as
   `WithTop.coe_le_coe.mpr le_top`; the unadorned `le_top` proves
   `↑m <= ⊤` and does not fit.

4. The ladder budget. With

       ladderBound L []      m = L m
       ladderBound L (a::as) m = ladderBound L as (m + 1) + norm a * ladderBound L as m

   the budget is nonnegative for nonnegative `L` (`ladderBound_nonneg`) and
   majorizes every shifted product at every order:

       derivOrderL1 m (shiftedProduct nodes f)
         <= ladderBound (derivOrderL1 · f) nodes m

   (`derivOrderL1_shiftedProduct_le`), by induction on the node list,
   generalizing the order. Unfolding the two cases of the recursion is `rfl`
   (`ladderBound_nil`, `ladderBound_cons`), and `shiftedProduct (a :: as) f`
   is `derivativeShift (shiftedProduct as f) a` by `rfl` as well.

   Expanding the recursion (hand check on one and two nodes, not formalized
   here) gives the closed form

       sum over k of mom_k * L (m + n - k),   n = number of nodes,

   where `mom_k` is the elementary symmetric polynomial of degree `k` in the
   node moduli `norm a_i`. The ladder index therefore moves opposite to the
   moment degree: the full product of node moduli multiplies the lowest order
   `L m`, and the empty product multiplies the top order `L (m + n)`. The
   naive recursion that adds `L (m + 1)` at every node does not reproduce the
   one- and two-node cases.

5. Seed-level consumers. For every node list and seed,

       l1Mass (shiftedProduct nodes f) <= ladderBound (derivOrderL1 · f) nodes 0

   directly (`l1Mass_shiftedProduct_le_ladder`, via `derivOrderL1_zero`) and
   through the committed consumer `l1Mass_shifted_product_le_of_budget`
   (`l1Mass_shiftedProduct_le_of_ladder`), whose step condition is
   discharged by the recursion itself. For a one-node list the budget is
   exactly the committed step `derivativeL1 f + norm a * l1Mass f`, so the
   ladder is consistent with the committed interface rather than a
   replacement for it.

6. Why a ladder is needed at all. The committed `shiftedProductL1Bound` feeds
   `derivativeL1 (shiftedProduct as f)` back into its own recursion, which is
   circular as a closed budget: the step for a suffix asks for the derivative
   budget of that suffix, not of the seed. The ladder is the honest recursion:
   one number per derivative order, every one of them a mass of the seed
   itself.

7. Order-`m` support-times-sup budget: given a support radius `B` and a sup
   norm `M` for the `m`-th derivative of the seed,

       derivOrderL1 m f <= (2 * B) * M

   (`derivOrderL1_le_of_support_of_norm_le`), the order-`m` form of the
   committed `derivativeL1_le_of_support_of_norm_le` used for record 1969.
   The committed order-one form carries `0 <= M` as a hypothesis; here it
   would be redundant, since `hbound` evaluated at a point outside the
   support interval already forces `0 <= M`, so the hypothesis is not stated.

## Evidence

- Module: ConnesWeilRH/Dev/C1ExplicitDerivativeLadder.lean
- Audit: ConnesWeilRH/Dev/C1ExplicitDerivativeLadderAudit.lean
- Build: lake build ConnesWeilRH.Dev.C1ExplicitDerivativeLadder
  ConnesWeilRH.Dev.C1ExplicitDerivativeLadderAudit
- Build completed successfully (3641 jobs); zero error lines, zero sorryAx,
  no warnings in the two new modules.
- All 13 audited declarations use only propext, Classical.choice, and
  Quot.sound.

## Still open

- No numerical value is chosen for the ladder at any concrete seed or node
  list; the ladder is a reduction, not a budget.
- The node-product constants, the strip contraction, the numerical
  cardinalRaw budget at a concrete node set, the correction quadratic
  margin, the signed determinant, and the joint tail margin stay open.
  Therefore RH remains unproved.
