/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCutoffTraceAnomaly

namespace ConnesWeilRH.Dev.CCM24FiniteSCutoffTraceAnomalyAudit

open ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCutoffTraceAnomaly

#check @coordinateProjection
#check @trace_mul_coordinateProjection_eq_sum
#check @trace_mul_coordinateProjection_eq_card_mul
#check @coordinateProjection_response_eq_card_sub_mul
#check @equalCard_coordinateProjection_response_eq_zero
#check @trace_mul_coordinateProjection_sub_eq_zero
#check @trace_commuting_similarity_eq

#print axioms trace_mul_coordinateProjection_eq_sum
#print axioms trace_mul_coordinateProjection_eq_card_mul
#print axioms coordinateProjection_response_eq_card_sub_mul
#print axioms equalCard_coordinateProjection_response_eq_zero
#print axioms trace_mul_coordinateProjection_sub_eq_zero
#print axioms trace_commuting_similarity_eq

end ConnesWeilRH.Dev.CCM24FiniteSCutoffTraceAnomalyAudit
