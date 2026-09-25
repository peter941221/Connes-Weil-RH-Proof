/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/
import ConnesWeilRH.Dev.C1GevreyVerticalDecayRung2

/-!
# Axiom audit for the rung-2 vertical-decay brick

Every public declaration of `ConnesWeilRH.Dev.C1GevreyVerticalDecayRung2`
must report exactly `[propext, Classical.choice, Quot.sound]`.
-/

#print axioms gevreyDeriv2
#print axioms gevreyDeriv2_of_abs_lt
#print axioms gevreyDeriv2_of_one_le_abs
#print axioms gevreyDeriv2_even
#print axioms gevreyDeriv_hasDerivAt_of_abs_lt
#print axioms abs_gevreyDeriv2_le_quartic
#print axioms continuous_gevreyDeriv2
#print axioms intervalIntegrable_gevreyDeriv2
#print axioms gevreyDeriv2_nonneg_of_mem_Icc_right
#print axioms gevreyDeriv2_nonneg_of_mem_Icc_left
#print axioms integral_abs_gevreyDeriv2_outer_right
#print axioms integral_abs_gevreyDeriv2_outer_left
#print axioms abs_gevreyDeriv2_le_mid
#print axioms integral_abs_gevreyDeriv2_le
#print axioms laplace_abs_le_rung2
#print axioms laplace_abs_le_rung2_vertical
