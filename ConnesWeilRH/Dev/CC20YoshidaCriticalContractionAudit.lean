/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20YoshidaCriticalContraction

/-!
# Critical-line Yoshida contraction import audit
-/

namespace ConnesWeilRH
namespace Dev
namespace CC20YoshidaCriticalContractionAudit

open Source.CC20YoshidaCriticalContraction.CompactLogTest

#check @translate
#check @laplaceAt_translate
#check @centeredPair
#check @laplaceAt_centeredPair
#check @exp_mul_I_eq_one_of_mul_eq_nat_two_pi
#check @centered_exponential_sum_eq_two_cosh_of_phase
#check @l1Mass
#check @l1Mass_translate_eq
#check @l1Mass_centeredPair_le
#check @norm_laplaceAt_mul_I_le_l1Mass
#check @norm_laplaceAt_centeredPair_mul_I_le
#check @laplaceAt_centeredPair_eq_one
#check @laplaceAt_centeredPair_eq_one_of_phase
#check @laplaceAt_centeredPair_eq_one_on_fourPointOrbit
#check @rawOfCentered
#check @laplaceAt_rawOfCentered
#check @laplaceAt_rawOfCentered_critical
#check @norm_laplaceAt_raw_centeredPair_critical_le

#print l1Mass_centeredPair_le
#print laplaceAt_centeredPair_eq_one_of_phase
#print laplaceAt_centeredPair_eq_one_on_fourPointOrbit
#print norm_laplaceAt_raw_centeredPair_critical_le

#print axioms laplaceAt_translate
#print axioms laplaceAt_centeredPair
#print axioms exp_mul_I_eq_one_of_mul_eq_nat_two_pi
#print axioms centered_exponential_sum_eq_two_cosh_of_phase
#print axioms l1Mass_translate_eq
#print axioms l1Mass_centeredPair_le
#print axioms norm_laplaceAt_mul_I_le_l1Mass
#print axioms norm_laplaceAt_centeredPair_mul_I_le
#print axioms laplaceAt_centeredPair_eq_one_of_phase
#print axioms laplaceAt_centeredPair_eq_one_on_fourPointOrbit
#print axioms laplaceAt_rawOfCentered
#print axioms laplaceAt_rawOfCentered_critical
#print axioms norm_laplaceAt_raw_centeredPair_critical_le

end CC20YoshidaCriticalContractionAudit
end Dev
end ConnesWeilRH
