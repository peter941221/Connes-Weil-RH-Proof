/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3SameOwnerGateNormalForm

/-!
# Audit for the ρ5 same-owner gate normal form
-/

namespace ConnesWeilRH
namespace Dev

section Audit

open Source.CC20Concrete
open Source.CCM25Concrete

#check @g8ReadbackRealTrace
#check @tendsto_g8ReadbackRealTrace_of_survivorCore
#check @g8R5_readbackTendsto_iff_aggregateLimit_eq_qw
#check @g8R5ZeroRemainderReadbackData
#check @g8R5_aggregateLimit_eq_qw_of_sameOwnerReadbackData

#print axioms g8ReadbackRealTrace
#print axioms tendsto_g8ReadbackRealTrace_of_survivorCore
#print axioms g8R5_readbackTendsto_iff_aggregateLimit_eq_qw
#print axioms g8R5ZeroRemainderReadbackData
#print axioms g8R5_aggregateLimit_eq_qw_of_sameOwnerReadbackData

end Audit

end Dev
end ConnesWeilRH
