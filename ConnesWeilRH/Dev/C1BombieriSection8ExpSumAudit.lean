/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8ExpSum

/-!
# Audit for the exponential-integral leaf

Focused axiom prints for the public declarations of the finite-window
exponential-integral slice.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8ExpSumAudit

#print axioms ConnesWeilRH.Source.C1BombieriSection8ExpSum.hasDerivAt_sin_mul_real
#print axioms ConnesWeilRH.Source.C1BombieriSection8ExpSum.hasDerivAt_cos_mul_real
#print axioms ConnesWeilRH.Source.C1BombieriSection8ExpSum.exp_i_mul_real
#print axioms ConnesWeilRH.Source.C1BombieriSection8ExpSum.integral_cos_mul_real
#print axioms ConnesWeilRH.Source.C1BombieriSection8ExpSum.integral_sin_mul_real
#print axioms ConnesWeilRH.Source.C1BombieriSection8ExpSum.integral_exp_i_window
#print axioms ConnesWeilRH.Source.C1BombieriSection8ExpSum.integral_exp_i_window_zero

end C1BombieriSection8ExpSumAudit
end Source
end ConnesWeilRH
