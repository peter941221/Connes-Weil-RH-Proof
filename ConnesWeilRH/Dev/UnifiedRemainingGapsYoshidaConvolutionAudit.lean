/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20YoshidaConvolution

/-!
# Plan 016 Yoshida convolution import audit
-/

namespace ConnesWeilRH
namespace Dev
namespace UnifiedRemainingGapsYoshidaConvolutionAudit

open Source.CC20YoshidaConvolution.CompactLogTest

#check @convolution_support_subset_add_Ioo
#check @laplaceAt_convolution
#check @laplaceAt_convolutionIterate
#check @convolutionIterate_support_subset_Ioo

#print laplaceAt_convolution
#print laplaceAt_convolutionIterate
#print convolutionIterate_support_subset_Ioo

#print axioms convolution_support_subset_add_Ioo
#print axioms laplaceAt_convolution
#print axioms laplaceAt_convolutionIterate
#print axioms convolutionIterate_support_subset_Ioo

end UnifiedRemainingGapsYoshidaConvolutionAudit
end Dev
end ConnesWeilRH
