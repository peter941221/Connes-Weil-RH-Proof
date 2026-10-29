import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceDataBridge
import ConnesWeilRH.Dev.AmbientSourceWeilFormSeam
import ConnesWeilRH.Dev.AmbientPrimeVisibleProbe

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace IndexedProducerFixedPoint3160

open AnalyticCore
open CCM25Concrete
open CCM25Concrete.FinitePrimeSourceData
open AmbientSeam
open AmbientPrimeProbe

noncomputable def ambientCommonTest :
    CommonSourceTest.ConcreteCommonSourceTest ambientWeilForm.toWeilFormSymbols :=
  CommonSourceTest.concreteCommonSourceTest
    ambientWeilForm.toWeilFormSymbols commonBump

theorem ambientCommonTest_source_read_off :
    ambientCommonTest.sourceTest = commonBump :=
  rfl

noncomputable def ambientVisibleData (lambda : ℝ) (hlambda : 1 < lambda) :
    FixedLambdaSourceWeilFormVisibleArithmeticData
      ambientWeilForm ambientCommonTest lambda :=
  { oneLtLambda := hlambda }

noncomputable def ambientSupportData (lambda : ℝ) (hlambda : 1 < lambda)
    (hAnchor :
      ambientSourceAlgebra.legacy.encode ambientWeilForm.common =
        ambientWeilForm.toWeilFormSymbols.convolutionStar
          ambientCommonTest.sourceTest ambientCommonTest.sourceTest) :
    FixedLambdaCommonFinitePrimeSupportData
      ambientWeilForm.toWeilFormSymbols ambientCommonTest lambda :=
  (ambientVisibleData lambda hlambda).toSupportData hAnchor

theorem ambientSupportData_globalIndexData
    (lambda : ℝ) (hlambda : 1 < lambda) :
    ∀ hAnchor :
      ambientSourceAlgebra.legacy.encode ambientWeilForm.common =
        ambientWeilForm.toWeilFormSymbols.convolutionStar
          ambientCommonTest.sourceTest ambientCommonTest.sourceTest,
    ∀ n : ℕ, n ∈ ambientWeilForm.toWeilFormSymbols.globalPrimeIndexSet →
      PrimePowerSupport.SourceGlobalIndexData
        ambientWeilForm.toWeilFormSymbols
        ambientCommonTest.sourceTest ambientCommonTest.sourceTest n :=
  fun hAnchor n hn => (ambientSupportData lambda hlambda hAnchor).globalIndexData n hn

theorem ambientSupportData_restrictedIndexData
    (lambda : ℝ) (hlambda : 1 < lambda) :
    ∀ hAnchor :
      ambientSourceAlgebra.legacy.encode ambientWeilForm.common =
        ambientWeilForm.toWeilFormSymbols.convolutionStar
          ambientCommonTest.sourceTest ambientCommonTest.sourceTest,
    ∀ n : ℕ, n ∈
        ambientWeilForm.toWeilFormSymbols.restrictedPrimeIndexSet lambda →
      PrimePowerSupport.SourceRestrictedIndexData
        ambientWeilForm.toWeilFormSymbols
        ambientCommonTest.sourceTest ambientCommonTest.sourceTest lambda n :=
  fun hAnchor n hn => (ambientSupportData lambda hlambda hAnchor).restrictedIndexData n hn

end IndexedProducerFixedPoint3160
end Dev
end Source
end ConnesWeilRH
