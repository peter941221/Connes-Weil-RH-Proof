import ConnesWeilRH.Dev.C1CC20ArchimedeanComparisonH143

namespace ConnesWeilRH
namespace Source
namespace C1CC20ArchimedeanComparisonH143Audit

open C1CC20ArchimedeanComparisonH143
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution

#print axioms cc20AuxiliaryNegTwo
#print axioms support_cc20AuxiliaryNegTwo_subset
#print axioms laplaceAt_cc20AuxiliaryNegTwo
#print axioms laplaceAt_cc20AuxiliaryNegTwo_half_eq_zero_of_vanishes
#print axioms cc20Echain_iff_nonpos_of_vanishes
#print axioms cc20ArchimedeanComparison_of_h142_hEchain
#print axioms cc20ArchimedeanComparison_of_h142_eNonpos
#print axioms qw_nonneg_of_h142_hEchain
#print axioms qw_nonneg_of_h142_eNonpos

example (g : CompactLogTest) (s : ℂ) :
    laplaceAt (cc20AuxiliaryNegTwo g) s =
      -(2 : ℂ) • laplaceAt g s :=
  laplaceAt_cc20AuxiliaryNegTwo g s

end C1CC20ArchimedeanComparisonH143Audit
end Source
end ConnesWeilRH
