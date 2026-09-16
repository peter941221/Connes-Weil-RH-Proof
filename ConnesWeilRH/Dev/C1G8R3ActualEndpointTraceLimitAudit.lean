/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ActualEndpointTraceLimit

/-!
# Audit for the actual endpoint channel trace limit
-/

namespace ConnesWeilRH
namespace Dev

section Audit

open Source.CC20Concrete
open Source.CCM25Concrete

#check @g8EndpointSourceCutoffOperator
#check @g8EndpointSourceCutoffLimitOperator
#check @g8EndpointSourceCutoffPairData_traceProduct_eq
#check @g8EndpointSourceCutoffOperator_inner_apply
#check @g8EndpointSourceCutoffLimitOperator_inner_apply
#check @tendsto_g8EndpointSourceCutoffOperator_inner_apply
#check @g8EndpointSourceCutoffOperator_inner_norm_le
#check @tendsto_g8EndpointSourceCutoffPairData_trace
#check @g8EndpointGate_iff_survivorCore
#check @tendsto_g8EndpointSourceCutoffPairData_trace_of_survivorCore

#print axioms g8EndpointSourceCutoffOperator
#print axioms g8EndpointSourceCutoffLimitOperator
#print axioms g8EndpointSourceCutoffPairData_traceProduct_eq
#print axioms g8EndpointSourceCutoffOperator_inner_apply
#print axioms g8EndpointSourceCutoffLimitOperator_inner_apply
#print axioms tendsto_g8EndpointSourceCutoffOperator_inner_apply
#print axioms g8EndpointSourceCutoffOperator_inner_norm_le
#print axioms tendsto_g8EndpointSourceCutoffPairData_trace
#print axioms g8EndpointGate_iff_survivorCore
#print axioms tendsto_g8EndpointSourceCutoffPairData_trace_of_survivorCore

end Audit

end Dev
end ConnesWeilRH
