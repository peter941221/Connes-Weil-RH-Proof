/-
Import-facing audit for the exact pole-free anti-maximum countermodel.
-/

import ConnesWeilRH.Dev.PolefreeAntimaxCounterexample

namespace ConnesWeilRH
namespace Dev
namespace PolefreeAntimaxCounterexampleAudit

open PolefreeAntimaxCounterexample

#check @A_mul_Ainv
#check @Ainv_mul_A
#check @Ainv_C
#check @C_dot_Ainv_C
#check @C_dot_v
#check @v_dot_Av
#check @inverse_scalar_positive_despite_negative_C_perp

#print axioms A_mul_Ainv
#print axioms Ainv_mul_A
#print axioms Ainv_C
#print axioms C_dot_Ainv_C
#print axioms C_dot_v
#print axioms v_dot_Av
#print axioms inverse_scalar_positive_despite_negative_C_perp

end PolefreeAntimaxCounterexampleAudit
end Dev
end ConnesWeilRH
