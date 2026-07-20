/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedQuotientCarrier

namespace ConnesWeilRH
namespace Dev

open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSFixedQuotientCarrier

#print axioms sourceBandProjection_isStarProjection
#print axioms sourceBandProjection_eq_starProjection
#print axioms sourceBandInclusion_adjoint_comp_self
#print axioms sourceBandInclusion_comp_adjoint
#print axioms sourceBandProjection_comp_sourceBandInclusion
#print axioms sourceBandProjection_comp_sourceInclusion_eq_zero
#print axioms sourceFixedQuotientCorner_on_sourceSoninCarrier_eq_zero
#print axioms sourceBandFixedQuotientCorner_eq_secondSupport_twoBranch
#print axioms sourceBandFixedQuotientFirstJetInputSideProducer_response_eq_corner

end Dev
end ConnesWeilRH
