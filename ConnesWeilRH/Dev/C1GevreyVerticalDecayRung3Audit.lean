/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/
import ConnesWeilRH.Dev.C1GevreyVerticalDecayRung3

/-!
# Axiom audit for the rung-3 vertical-decay brick

Every public declaration of `ConnesWeilRH.Dev.C1GevreyVerticalDecayRung3`
must report exactly `[propext, Classical.choice, Quot.sound]`.
-/

#print axioms gevreyDeriv3
#print axioms gevreyDeriv3_of_abs_lt
#print axioms gevreyDeriv3_of_one_le_abs
#print axioms gevreyDeriv2_hasDerivAt_of_abs_lt
#print axioms abs_gevreyDeriv3_le_septic
#print axioms continuous_gevreyDeriv3
#print axioms intervalIntegrable_gevreyDeriv3
#print axioms integral_abs_gevreyDeriv3_outer_right_le
#print axioms integral_abs_gevreyDeriv3_outer_left_le
#print axioms abs_gevreyDeriv3_le_mid
#print axioms integral_abs_gevreyDeriv3_le
#print axioms laplace_abs_le_rung3
#print axioms laplace_abs_le_rung3_vertical
