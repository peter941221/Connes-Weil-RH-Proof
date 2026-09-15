/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ActualCutoffPairedCrossTrace

namespace ConnesWeilRH
namespace Dev

#check @g8MetricCutoffSourceLeakageCrossOperator_eq_adjoint
#print axioms g8MetricCutoffSourceLeakageCrossOperator_eq_adjoint
#check @tendsto_ordinaryTraceAlong_g8MetricSourceLeakageCross_actualCutoff
#print axioms tendsto_ordinaryTraceAlong_g8MetricSourceLeakageCross_actualCutoff
#check @tendsto_ordinaryTraceAlong_g8MetricPairedCross_actualCutoff
#print axioms tendsto_ordinaryTraceAlong_g8MetricPairedCross_actualCutoff

end Dev
end ConnesWeilRH
