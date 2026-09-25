/-
Copyright (c) 2026. All rights reserved.
-/
import ConnesWeilRH.Dev.C1GevreyVerticalDecay

/-!
# Axiom audit for `C1GevreyVerticalDecay`

Every public declaration in `C1GevreyVerticalDecay.lean` is checked with
`#print axioms`.  Acceptance: each line reports exactly
`'propext', 'Classical.choice', 'Quot.sound'` (the standard Lean/Mathlib
axioms) and nothing else — in particular no `sorryAx`.
-/

open Real

#print axioms gevreyDeriv
#print axioms gevreyDeriv_of_abs_lt
#print axioms gevreyDeriv_of_one_le_abs
#print axioms abs_gevreyDeriv_le_quartic
#print axioms continuous_gevreyDeriv
#print axioms intervalIntegrable_gevreyDeriv
#print axioms gevreyDeriv_nonpos_of_mem_Icc
#print axioms gevreyDeriv_nonneg_of_mem_Icc
#print axioms integral_abs_gevreyDeriv_half_right
#print axioms integral_abs_gevreyDeriv_half_left
#print axioms abs_gevreyDeriv_le_mid
#print axioms integral_abs_gevreyDeriv_le
#print axioms hasDerivAt_complex_gevreyInner
#print axioms laplace_abs_le
#print axioms laplace_abs_le_vertical
