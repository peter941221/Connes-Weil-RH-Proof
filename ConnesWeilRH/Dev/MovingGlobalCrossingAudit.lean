/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.MovingGlobalCrossing

namespace ConnesWeilRH.Dev.MovingGlobalCrossingAudit

open ConnesWeilRH Source CC20Concrete

#check @cc20MovingSingleCrossingResponse
#check @cc20MovingSingleCrossingBoundaryIntegrand
#check @cc20MovingSingleCrossingResponse_eq_boundaryIntegral
#check @continuous_cc20MovingSingleCrossingResponse
#check @integrable_cc20MovingSingleCrossingResponse
#check @integral_cc20MovingSingleCrossingResponse_eq_boundaryIntegral

#print axioms cc20MovingSingleCrossingResponse_eq_boundaryIntegral
#print axioms continuous_cc20MovingSingleCrossingResponse
#print axioms integrable_cc20MovingSingleCrossingResponse
#print axioms integral_cc20MovingSingleCrossingResponse_eq_boundaryIntegral

end ConnesWeilRH.Dev.MovingGlobalCrossingAudit
