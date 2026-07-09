/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.Objects
import ConnesWeilRH.Source.ObjectTheoremBasePackage
import ConnesWeilRH.Source.CC20Concrete.TraceScale
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceDataBridge
import ConnesWeilRH.Source.CCM25Concrete.Package

/-!
# Source-object expanded row staging

Goal 2C groups the expanded row data needed by `SourceObjectPackage` without
constructing a full source-object package.  The CCM25 row is derived from the
same concrete arithmetic rows used by Goal 0E, while CCM24 and CC20 remain
explicit expanded-row inputs.
-/

namespace ConnesWeilRH
namespace Source

open CCM25Concrete
open CCM25Concrete.FinitePrimeCertificate
open CCM25Concrete.FinitePrimeSourceData

/--
Common source-test data for Goal 2C.

The record forces the CCM25 arithmetic rows to use the same source evaluator as
the common source test.  This is the equality that later fills the
`SourceObjectPackage.ccm25Test_eq_commonTest` field.
-/
structure SourceObjectCommonData
    (base : SourceObjectTheoremBasePackage) where
  commonTest :
    SourceObject.CommonTestObject base.ccm25Model.toWeilFormSymbols
  concreteArithmeticRows :
    CCM25Concrete.Interface.ConcreteCCM25ArithmeticRows
      base.ccm25Model.toWeilFormSymbols
  ccm25Test_eq_commonTest :
    commonTest.ccm25SourceTest =
      CCM25Concrete.Rows.source_test_of_arithmetic_rows
        concreteArithmeticRows commonTest.sourceTest commonTest.sourceTest
  commonFinitePrimeArithmeticSourceDataOwner :
    CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
      base.ccm25Model.toWeilFormSymbols
  commonFinitePrimeArithmeticSourceData_commonTest :
    commonFinitePrimeArithmeticSourceDataOwner.commonTestFunction =
      commonTest.sourceTest

/--
Concrete common-test data for Goal 2C.

This is the narrow Block 1 seed below `SourceObjectCommonData`: it fixes the
common source test first, then requires the CCM25 arithmetic rows to expose the
same source-test interface at the pair `(g,g)`.  It avoids constructing a full
`SourceObjectPackage`, whose CCM24/CC20/RH-exit fields remain separate
analytic obligations.
-/
structure SourceObjectConcreteCommonData
    (base : SourceObjectTheoremBasePackage) where
  concreteCommonTest :
    CCM25Concrete.CommonSourceTest.ConcreteCommonSourceTest
      base.ccm25Model.toWeilFormSymbols
  concreteArithmeticRows :
    CCM25Concrete.Interface.ConcreteCCM25ArithmeticRows
      base.ccm25Model.toWeilFormSymbols
  arithmeticRowsUseConcreteCommonTest :
    CCM25Concrete.Rows.source_test_of_arithmetic_rows
        concreteArithmeticRows concreteCommonTest.sourceTest
        concreteCommonTest.sourceTest =
      concreteCommonTest.toSourceTestEvaluationInterface
  commonFinitePrimeArithmeticSourceDataOwner :
    CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
      base.ccm25Model.toWeilFormSymbols
  commonFinitePrimeArithmeticSourceData_commonTest :
    commonFinitePrimeArithmeticSourceDataOwner.commonTestFunction =
      concreteCommonTest.sourceTest
  commonFinitePrimeArithmeticSourceData_commonPairSourceTest :
    commonFinitePrimeArithmeticSourceDataOwner.finitePrimeData.selector.sourceTest
        concreteCommonTest.sourceTest concreteCommonTest.sourceTest =
      concreteCommonTest.toSourceTestEvaluationInterface
  commonFinitePrimeArithmeticSourceData_scopedArchimedeanContributionBalance :
    ∀ lambda : ℝ,
      ∀ globalData :
        CCM25Concrete.PrimePowerArithmetic.SourceGlobalFinitePrimeArithmeticData
          base.ccm25Model.toWeilFormSymbols concreteCommonTest.sourceTest
          concreteCommonTest.sourceTest,
      ∀ restrictedData :
        CCM25Concrete.PrimePowerArithmetic.SourceRestrictedFinitePrimeArithmeticData
          base.ccm25Model.toWeilFormSymbols concreteCommonTest.sourceTest
          concreteCommonTest.sourceTest lambda,
        CCM25Concrete.FinitePrimeSourceData.SourceScopedArchimedeanContributionBalance
          base.ccm25Model.toWeilFormSymbols concreteCommonTest.sourceTest lambda
          globalData restrictedData

namespace SourceObjectConcreteCommonData

open CCM25Concrete
open CCM25Concrete.FinitePrimeSourceData

def ofSameSourceTest
    {base : SourceObjectTheoremBasePackage}
    (common :
      CCM25Concrete.CommonSourceTest.ConcreteCommonSourceTest
        base.ccm25Model.toWeilFormSymbols)
    (rows :
      CCM25Concrete.Interface.ConcreteCCM25ArithmeticRows
        base.ccm25Model.toWeilFormSymbols)
    (sameSourceTest :
      CCM25Concrete.Rows.source_test_of_arithmetic_rows
          rows common.sourceTest common.sourceTest =
        common.toSourceTestEvaluationInterface)
    (commonFinitePrimeArithmeticSourceData :
      CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
        base.ccm25Model.toWeilFormSymbols)
    (commonFinitePrimeArithmeticSourceData_commonTest :
      commonFinitePrimeArithmeticSourceData.commonTestFunction =
        common.sourceTest)
    (commonFinitePrimeArithmeticSourceData_commonPairSourceTest :
      commonFinitePrimeArithmeticSourceData.finitePrimeData.selector.sourceTest
          common.sourceTest common.sourceTest =
        common.toSourceTestEvaluationInterface)
    (commonFinitePrimeArithmeticSourceData_scopedArchimedeanContributionBalance :
      ∀ lambda : ℝ,
        ∀ globalData :
          CCM25Concrete.PrimePowerArithmetic.SourceGlobalFinitePrimeArithmeticData
            base.ccm25Model.toWeilFormSymbols common.sourceTest common.sourceTest,
        ∀ restrictedData :
          CCM25Concrete.PrimePowerArithmetic.SourceRestrictedFinitePrimeArithmeticData
            base.ccm25Model.toWeilFormSymbols common.sourceTest common.sourceTest
            lambda,
          CCM25Concrete.FinitePrimeSourceData.SourceScopedArchimedeanContributionBalance
            base.ccm25Model.toWeilFormSymbols common.sourceTest lambda
            globalData restrictedData) :
    SourceObjectConcreteCommonData base where
  concreteCommonTest := common
  concreteArithmeticRows := rows
  arithmeticRowsUseConcreteCommonTest := sameSourceTest
  commonFinitePrimeArithmeticSourceDataOwner := commonFinitePrimeArithmeticSourceData
  commonFinitePrimeArithmeticSourceData_commonTest :=
    commonFinitePrimeArithmeticSourceData_commonTest
  commonFinitePrimeArithmeticSourceData_commonPairSourceTest :=
    commonFinitePrimeArithmeticSourceData_commonPairSourceTest
  commonFinitePrimeArithmeticSourceData_scopedArchimedeanContributionBalance :=
    commonFinitePrimeArithmeticSourceData_scopedArchimedeanContributionBalance

def ofCommonPairSourceTest
    {base : SourceObjectTheoremBasePackage}
    (common :
      CCM25Concrete.CommonSourceTest.ConcreteCommonSourceTest
        base.ccm25Model.toWeilFormSymbols)
    (rows :
      CCM25Concrete.Interface.ConcreteCCM25ArithmeticRows
        base.ccm25Model.toWeilFormSymbols)
    (commonPairSourceTest :
      (rows.finitePrimeArithmeticCertificates
          common.sourceTest common.sourceTest).sourceTest =
        common.toSourceTestEvaluationInterface)
    (commonFinitePrimeArithmeticSourceData :
      CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
        base.ccm25Model.toWeilFormSymbols)
    (commonFinitePrimeArithmeticSourceData_commonTest :
      commonFinitePrimeArithmeticSourceData.commonTestFunction =
        common.sourceTest)
    (commonFinitePrimeArithmeticSourceData_commonPairSourceTest :
      commonFinitePrimeArithmeticSourceData.finitePrimeData.selector.sourceTest
          common.sourceTest common.sourceTest =
        common.toSourceTestEvaluationInterface)
    (commonFinitePrimeArithmeticSourceData_scopedArchimedeanContributionBalance :
      ∀ lambda : ℝ,
        ∀ globalData :
          CCM25Concrete.PrimePowerArithmetic.SourceGlobalFinitePrimeArithmeticData
            base.ccm25Model.toWeilFormSymbols common.sourceTest common.sourceTest,
        ∀ restrictedData :
          CCM25Concrete.PrimePowerArithmetic.SourceRestrictedFinitePrimeArithmeticData
            base.ccm25Model.toWeilFormSymbols common.sourceTest common.sourceTest
            lambda,
          CCM25Concrete.FinitePrimeSourceData.SourceScopedArchimedeanContributionBalance
            base.ccm25Model.toWeilFormSymbols common.sourceTest lambda
            globalData restrictedData) :
    SourceObjectConcreteCommonData base :=
  ofSameSourceTest common rows (by
    simpa [CCM25Concrete.Rows.source_test_of_arithmetic_rows]
      using commonPairSourceTest)
    commonFinitePrimeArithmeticSourceData
    commonFinitePrimeArithmeticSourceData_commonTest
    commonFinitePrimeArithmeticSourceData_commonPairSourceTest
    commonFinitePrimeArithmeticSourceData_scopedArchimedeanContributionBalance

def ofCanonicalFinitePrimeOwner
    {base : SourceObjectTheoremBasePackage}
    (rows :
      CCM25Concrete.Interface.ConcreteCCM25ArithmeticRows
        base.ccm25Model.toWeilFormSymbols)
    (commonFinitePrimeArithmeticSourceData :
      CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
        base.ccm25Model.toWeilFormSymbols)
    (sameSourceTest :
      CCM25Concrete.Rows.source_test_of_arithmetic_rows rows
          commonFinitePrimeArithmeticSourceData.commonTestFunction
          commonFinitePrimeArithmeticSourceData.commonTestFunction =
        (CCM25Concrete.CommonSourceTest.concreteCommonSourceTest
          base.ccm25Model.toWeilFormSymbols
          commonFinitePrimeArithmeticSourceData.commonTestFunction).toSourceTestEvaluationInterface) :
    SourceObjectConcreteCommonData base :=
  ofSameSourceTest
    (CCM25Concrete.CommonSourceTest.concreteCommonSourceTest
      base.ccm25Model.toWeilFormSymbols
      commonFinitePrimeArithmeticSourceData.commonTestFunction)
    rows sameSourceTest commonFinitePrimeArithmeticSourceData rfl
    (CCM25Concrete.FinitePrimeSourceData.commonPairSourceTest
      commonFinitePrimeArithmeticSourceData)
    commonFinitePrimeArithmeticSourceData.scopedArchimedeanContributionBalance

def commonTest
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    SourceObject.CommonTestObject base.ccm25Model.toWeilFormSymbols :=
  SourceObject.CommonTestObject.ofConcrete data.concreteCommonTest

def toSourceObjectCommonData
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    SourceObjectCommonData base where
  commonTest := data.commonTest
  concreteArithmeticRows := data.concreteArithmeticRows
  ccm25Test_eq_commonTest := data.arithmeticRowsUseConcreteCommonTest.symm
  commonFinitePrimeArithmeticSourceDataOwner :=
    data.commonFinitePrimeArithmeticSourceDataOwner
  commonFinitePrimeArithmeticSourceData_commonTest := by
    simpa [SourceObject.CommonTestObject.ofConcrete]
      using data.commonFinitePrimeArithmeticSourceData_commonTest

theorem common_test_eq_of_concrete
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    (data.toSourceObjectCommonData).commonTest =
      SourceObject.CommonTestObject.ofConcrete data.concreteCommonTest :=
  rfl

theorem source_test_eq_concrete
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    (data.toSourceObjectCommonData).commonTest.sourceTest =
      data.concreteCommonTest.sourceTest :=
  rfl

theorem source_convolution_square_eq_concrete
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    (data.toSourceObjectCommonData).commonTest.sourceConvolutionSquare =
      data.concreteCommonTest.sourceConvolutionSquare :=
  rfl

theorem ccm25_source_test_eq_concrete
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    (data.toSourceObjectCommonData).commonTest.ccm25SourceTest =
      data.concreteCommonTest.toSourceTestEvaluationInterface :=
  rfl

theorem arithmetic_rows_source_test_eq_concrete
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    CCM25Concrete.Rows.source_test_of_arithmetic_rows
        data.concreteArithmeticRows data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest =
      data.concreteCommonTest.toSourceTestEvaluationInterface :=
  data.arithmeticRowsUseConcreteCommonTest

theorem common_finite_prime_source_test_pair_eq_concrete
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    (data.commonFinitePrimeArithmeticSourceDataOwner.finitePrimeData.selector.sourceTest
        data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest) =
      data.concreteCommonTest.toSourceTestEvaluationInterface :=
  by
    exact data.commonFinitePrimeArithmeticSourceData_commonPairSourceTest

def commonFixedLambdaArithmeticCertificateData
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    CCM25Concrete.FinitePrimeSourceData.FixedLambdaArithmeticCertificateSourceTestData
      base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest lambda
      (data.commonFinitePrimeArithmeticSourceDataOwner.finitePrimeData.selector.sourceTest
        data.concreteCommonTest.sourceTest data.concreteCommonTest.sourceTest) :=
  data.commonFinitePrimeArithmeticSourceDataOwner.finitePrimeData.certificateData
    data.concreteCommonTest.sourceTest data.concreteCommonTest.sourceTest
    lambda hlambda

theorem common_fixed_lambda_arithmetic_data_source_test_eq_concrete
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    ((data.commonFixedLambdaArithmeticCertificateData lambda hlambda).toSupport
        hlambda).sourceTest =
      data.concreteCommonTest.toSourceTestEvaluationInterface := by
  exact data.common_finite_prime_source_test_pair_eq_concrete

def commonArithmeticCertificate
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    CCM25Concrete.FinitePrimeCertificate.FixedLambdaFinitePrimeArithmeticCertificate
      base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest lambda :=
  (data.commonFixedLambdaArithmeticCertificateData lambda hlambda).toCertificate
    hlambda

/--
Common fixed-lambda support data for the concrete source test.

This is the lower support object below the common finite-prime source rows.
Consumers that only need support, visibility, and cutoff data should use this
instead of reading those rows back from the full arithmetic certificate.
-/
def commonFixedLambdaPrimePowerSupport
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    CCM25Concrete.PrimePowerSupport.ConcreteCommonFixedLambdaPrimePowerSupport
      base.ccm25Model.toWeilFormSymbols data.concreteCommonTest lambda where
  support :=
    (data.commonFixedLambdaArithmeticCertificateData lambda hlambda).toSupport
      hlambda
  sourceTestReadOff :=
    data.common_fixed_lambda_arithmetic_data_source_test_eq_concrete
      lambda hlambda

def commonFixedLambdaFinitePrimeSupportData
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    CCM25Concrete.FinitePrimeSourceData.FixedLambdaCommonFinitePrimeSupportData
      base.ccm25Model.toWeilFormSymbols data.concreteCommonTest lambda :=
  FixedLambdaCommonFinitePrimeSupportData.ofConcreteCommonSupport
    (data.commonFixedLambdaPrimePowerSupport lambda hlambda)

noncomputable def commonArithmeticPackage
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
      base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
      lambda where
  rows := data.concreteArithmeticRows
  oneLtLambda := hlambda

noncomputable def transportFixedLambdaSourceTestData
    {W W' : WeilFormSymbols}
    (hW : W = W')
    (common : CCM25Concrete.CommonSourceTest.ConcreteCommonSourceTest W)
    {lambda : ℝ}
    (sourceData :
      CCM25Concrete.FinitePrimeSourceData.FixedLambdaArithmeticCertificateSourceTestData
        W' (hW ▸ common).sourceTest (hW ▸ common).sourceTest lambda
        (hW ▸ common).toSourceTestEvaluationInterface) :
    CCM25Concrete.FinitePrimeSourceData.FixedLambdaArithmeticCertificateSourceTestData
      W common.sourceTest common.sourceTest lambda
      common.toSourceTestEvaluationInterface := by
  subst hW
  exact sourceData

noncomputable def transportSourceFinitePrimeArithmeticData
    {W W' : WeilFormSymbols}
    (hW : W = W')
    (common : CCM25Concrete.CommonSourceTest.ConcreteCommonSourceTest W)
    {n : ℕ}
    (sourceData :
      CCM25Concrete.PrimePowerArithmetic.SourceFinitePrimeArithmeticData
        W' (hW ▸ common).sourceTest (hW ▸ common).sourceTest n) :
    CCM25Concrete.PrimePowerArithmetic.SourceFinitePrimeArithmeticData
      W common.sourceTest common.sourceTest n := by
  subst hW
  exact sourceData

theorem transport_sourceAtomVisible
    {W W' : WeilFormSymbols}
    (hW : W = W')
    (common : CCM25Concrete.CommonSourceTest.ConcreteCommonSourceTest W)
    {n : ℕ}
    (hn : common.toSourceTestEvaluationInterface.sourceAtomVisible n) :
    (hW ▸ common).toSourceTestEvaluationInterface.sourceAtomVisible n := by
  subst hW
  exact hn

theorem transport_routeFinitePrimeAtomVisible
    {W W' : WeilFormSymbols}
    (hW : W = W')
    (common : CCM25Concrete.CommonSourceTest.ConcreteCommonSourceTest W)
    {n : ℕ}
    (hvisible :
      W.finitePrimeAtomVisible n
        (W.convolutionStar common.sourceTest common.sourceTest)) :
    W'.finitePrimeAtomVisible n
      (W'.convolutionStar
        (hW ▸ common).sourceTest (hW ▸ common).sourceTest) := by
  subst hW
  exact hvisible

theorem transport_finitePrimeAtomVisible_convolution
    {W W' : WeilFormSymbols}
    (hW : W = W')
    (f g : TestFunction)
    {n : ℕ}
    (hvisible :
      W.finitePrimeAtomVisible n (W.convolutionStar f g)) :
    W'.finitePrimeAtomVisible n (W'.convolutionStar f g) := by
  subst hW
  exact hvisible

theorem transport_globalPrimeIndex_mem
    {W W' : WeilFormSymbols}
    (hW : W = W')
    {n : ℕ}
    (hn : n ∈ W.globalPrimeIndexSet) :
    n ∈ W'.globalPrimeIndexSet := by
  subst hW
  exact hn

theorem transport_restrictedPrimeIndex_mem
    {W W' : WeilFormSymbols}
    (hW : W = W')
    (lambda : ℝ)
    {n : ℕ}
    (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    n ∈ W'.restrictedPrimeIndexSet lambda := by
  subst hW
  exact hn

theorem transport_finitePrimeTerm_normalization
    {W W' : WeilFormSymbols}
    (hW : W = W')
    (f g : TestFunction)
    (n : ℕ)
    (hterm :
      W'.finitePrimeTerm n (W'.convolutionStar f g) =
        W'.vonMangoldtWeight n * W'.primePowerPairing n f g) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      W.vonMangoldtWeight n * W.primePowerPairing n f g := by
  subst hW
  exact hterm

structure SourceEvaluationVisibleFinitePrimeBoundary
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) where
  sourceAlgebra : AnalyticCore.SourceTestAlgebra
  sourceWeilForm : AnalyticCore.SourceWeilFormData sourceAlgebra
  sourceSymbols_eq :
    base.ccm25Model.toWeilFormSymbols = sourceWeilForm.toWeilFormSymbols
  oneLtLambda : 1 < lambda

namespace SourceEvaluationVisibleFinitePrimeBoundary

noncomputable def supportDataOfSourceWeilForm
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    {sourceAlgebra : AnalyticCore.SourceTestAlgebra}
    (sourceWeilForm : AnalyticCore.SourceWeilFormData sourceAlgebra)
    (sourceSymbols_eq :
      base.ccm25Model.toWeilFormSymbols =
        sourceWeilForm.toWeilFormSymbols)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    CCM25Concrete.FinitePrimeSourceData.FixedLambdaCommonFinitePrimeSupportData
      sourceWeilForm.toWeilFormSymbols
      (sourceSymbols_eq ▸ data.concreteCommonTest) lambda := by
  let common := sourceSymbols_eq ▸ data.concreteCommonTest
  let visibleData :
      CCM25Concrete.FinitePrimeSourceData.FixedLambdaSourceWeilFormVisibleArithmeticData
        sourceWeilForm common lambda :=
    { oneLtLambda := hlambda }
  refine
    { globalIndexData := ?_
      routeVisibleGlobalIndex := ?_
      restrictedIndexData := ?_
      routeVisibleRestrictedIndex := ?_ }
  · intro n hn
    exact (visibleData.globalExact n).1 hn
  · intro n hvisible
    have hsourceVisible :
        common.toSourceTestEvaluationInterface.sourceAtomVisible n :=
      (common.route_visibility_iff_source_visibility n).1 hvisible
    exact
      (visibleData.globalExact n).2
        { primePowerIndex :=
            visibleData.mathlibSourcePrimePowerIndex n hsourceVisible
          atomVisible := hsourceVisible }
  · intro n hn
    exact (visibleData.restrictedExact n).1 hn
  · intro n hvisible hOne hCutoff
    have hsourceVisible :
        common.toSourceTestEvaluationInterface.sourceAtomVisible n :=
      (common.route_visibility_iff_source_visibility n).1 hvisible
    exact
      (visibleData.restrictedExact n).2
        { primePowerIndex :=
            visibleData.mathlibSourcePrimePowerIndex n hsourceVisible
          atomVisible := hsourceVisible
          lambdaCut := ⟨hOne, hCutoff⟩ }

noncomputable def visibleDataOfSourceWeilForm
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    {sourceAlgebra : AnalyticCore.SourceTestAlgebra}
    (sourceWeilForm : AnalyticCore.SourceWeilFormData sourceAlgebra)
    (sourceSymbols_eq :
      base.ccm25Model.toWeilFormSymbols =
        sourceWeilForm.toWeilFormSymbols)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    CCM25Concrete.FinitePrimeSourceData.FixedLambdaSourceWeilFormVisibleArithmeticData
      sourceWeilForm (sourceSymbols_eq ▸ data.concreteCommonTest) lambda := by
  exact { oneLtLambda := hlambda }

noncomputable def supportData
    {base : SourceObjectTheoremBasePackage}
    {data : SourceObjectConcreteCommonData base}
    {lambda : ℝ}
    (boundary :
      SourceEvaluationVisibleFinitePrimeBoundary data lambda) :
    CCM25Concrete.FinitePrimeSourceData.FixedLambdaCommonFinitePrimeSupportData
      boundary.sourceWeilForm.toWeilFormSymbols
      (boundary.sourceSymbols_eq ▸ data.concreteCommonTest) lambda :=
  supportDataOfSourceWeilForm data boundary.sourceWeilForm
    boundary.sourceSymbols_eq lambda boundary.oneLtLambda

noncomputable def visibleData
    {base : SourceObjectTheoremBasePackage}
    {data : SourceObjectConcreteCommonData base}
    {lambda : ℝ}
    (boundary :
      SourceEvaluationVisibleFinitePrimeBoundary data lambda) :
    CCM25Concrete.FinitePrimeSourceData.FixedLambdaSourceWeilFormVisibleArithmeticData
      boundary.sourceWeilForm
      (boundary.sourceSymbols_eq ▸ data.concreteCommonTest) lambda :=
  visibleDataOfSourceWeilForm data boundary.sourceWeilForm
    boundary.sourceSymbols_eq lambda boundary.oneLtLambda

noncomputable def ofSourceWeilForm
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    {sourceAlgebra : AnalyticCore.SourceTestAlgebra}
    (sourceWeilForm : AnalyticCore.SourceWeilFormData sourceAlgebra)
    (sourceSymbols_eq :
      base.ccm25Model.toWeilFormSymbols =
        sourceWeilForm.toWeilFormSymbols)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    SourceEvaluationVisibleFinitePrimeBoundary data lambda where
  sourceAlgebra := sourceAlgebra
  sourceWeilForm := sourceWeilForm
  sourceSymbols_eq := sourceSymbols_eq
  oneLtLambda := hlambda

theorem mathlibSourcePrimePowerIndex
    {base : SourceObjectTheoremBasePackage}
    {data : SourceObjectConcreteCommonData base}
    {lambda : ℝ}
    (boundary :
      SourceEvaluationVisibleFinitePrimeBoundary data lambda)
    {n : ℕ}
    (hn :
      (boundary.sourceSymbols_eq ▸
        data.concreteCommonTest).toSourceTestEvaluationInterface.sourceAtomVisible n) :
    IsPrimePow n :=
  boundary.visibleData.mathlibSourcePrimePowerIndex n
    hn

theorem baseMathlibSourcePrimePowerIndex
    {base : SourceObjectTheoremBasePackage}
    {data : SourceObjectConcreteCommonData base}
    {lambda : ℝ}
    (boundary :
      SourceEvaluationVisibleFinitePrimeBoundary data lambda)
    {n : ℕ}
    (hn :
      data.concreteCommonTest.toSourceTestEvaluationInterface.sourceAtomVisible n) :
    IsPrimePow n :=
  boundary.mathlibSourcePrimePowerIndex
    (transport_sourceAtomVisible boundary.sourceSymbols_eq
      data.concreteCommonTest hn)

theorem globalExact
    {base : SourceObjectTheoremBasePackage}
    {data : SourceObjectConcreteCommonData base}
    {lambda : ℝ}
    (boundary :
      SourceEvaluationVisibleFinitePrimeBoundary data lambda)
    (n : ℕ) :
    n ∈ boundary.sourceWeilForm.toWeilFormSymbols.globalPrimeIndexSet ↔
      CCM25Concrete.PrimePowerSupport.SourceGlobalIndexData
        boundary.sourceWeilForm.toWeilFormSymbols
        (boundary.sourceSymbols_eq ▸ data.concreteCommonTest).sourceTest
        (boundary.sourceSymbols_eq ▸ data.concreteCommonTest).sourceTest n :=
  CCM25Concrete.FinitePrimeSourceData.FixedLambdaCommonFinitePrimeSupportData.globalExact
    boundary.supportData n

structure VisibleAtomInLambdaCutoffData
    {base : SourceObjectTheoremBasePackage}
    {data : SourceObjectConcreteCommonData base}
    {lambda : ℝ}
    (boundary :
      SourceEvaluationVisibleFinitePrimeBoundary data lambda)
    (n : ℕ) where
  restrictedMem :
    n ∈ boundary.sourceWeilForm.toWeilFormSymbols.restrictedPrimeIndexSet
      lambda
  routeVisible :
    boundary.sourceWeilForm.toWeilFormSymbols.finitePrimeAtomVisible n
      (boundary.sourceWeilForm.toWeilFormSymbols.convolutionStar
        (boundary.sourceSymbols_eq ▸ data.concreteCommonTest).sourceTest
        (boundary.sourceSymbols_eq ▸ data.concreteCommonTest).sourceTest)
  sourceVisible :
    (boundary.sourceSymbols_eq ▸
      data.concreteCommonTest).toSourceTestEvaluationInterface.sourceAtomVisible n
  lambdaCut :
    CCM25Concrete.PrimePowerSupport.SourceLambdaCut lambda n
  restrictedIndexData :
    CCM25Concrete.PrimePowerSupport.SourceRestrictedIndexData
      boundary.sourceWeilForm.toWeilFormSymbols
      (boundary.sourceSymbols_eq ▸ data.concreteCommonTest).sourceTest
      (boundary.sourceSymbols_eq ▸ data.concreteCommonTest).sourceTest lambda n
  sourceArithmeticData :
    CCM25Concrete.PrimePowerArithmetic.SourceFinitePrimeArithmeticData
      base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest n

noncomputable def visibleAtomInLambdaCutoffData
    {base : SourceObjectTheoremBasePackage}
    {data : SourceObjectConcreteCommonData base}
    {lambda : ℝ}
    (boundary :
      SourceEvaluationVisibleFinitePrimeBoundary data lambda)
    {n : ℕ}
    (hn :
      n ∈ base.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet
        lambda) :
    VisibleAtomInLambdaCutoffData boundary n := by
  have hn_source :
      n ∈ boundary.sourceWeilForm.toWeilFormSymbols.restrictedPrimeIndexSet
        lambda := by
    simpa [boundary.sourceSymbols_eq] using hn
  let hindex := boundary.supportData.restrictedIndexData n hn_source
  have hsourceVisible :
      (boundary.sourceSymbols_eq ▸
        data.concreteCommonTest).toSourceTestEvaluationInterface.sourceAtomVisible n :=
    hindex.atomVisible
  exact
    { restrictedMem := hn_source
      routeVisible := hindex.atomVisible
      sourceVisible := hsourceVisible
      lambdaCut := hindex.lambdaCut
      restrictedIndexData := hindex
      sourceArithmeticData :=
        transportSourceFinitePrimeArithmeticData boundary.sourceSymbols_eq
          data.concreteCommonTest
          (boundary.visibleData.toSourceEvaluationVisibleArithmeticData
            |>.visibleArithmeticData |>.atVisibleIndex n hsourceVisible) }

noncomputable def routeVisibleAtomInLambdaCutoffData
    {base : SourceObjectTheoremBasePackage}
    {data : SourceObjectConcreteCommonData base}
    {lambda : ℝ}
    (boundary :
      SourceEvaluationVisibleFinitePrimeBoundary data lambda)
    {n : ℕ}
    (hvisible :
      base.ccm25Model.toWeilFormSymbols.finitePrimeAtomVisible n
        (base.ccm25Model.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest data.concreteCommonTest.sourceTest))
    (hOne : 1 < n)
    (hCutoff : (n : ℝ) ≤ lambda ^ 2) :
    VisibleAtomInLambdaCutoffData boundary n := by
  have hsourceVisible :
      boundary.sourceWeilForm.toWeilFormSymbols.finitePrimeAtomVisible n
        (boundary.sourceWeilForm.toWeilFormSymbols.convolutionStar
          (boundary.sourceSymbols_eq ▸ data.concreteCommonTest).sourceTest
          (boundary.sourceSymbols_eq ▸ data.concreteCommonTest).sourceTest) :=
    transport_routeFinitePrimeAtomVisible boundary.sourceSymbols_eq
      data.concreteCommonTest hvisible
  have hn_source :
      n ∈ boundary.sourceWeilForm.toWeilFormSymbols.restrictedPrimeIndexSet
        lambda :=
    boundary.supportData.routeVisibleRestrictedIndex n hsourceVisible
      hOne hCutoff
  have hn :
      n ∈ base.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet
        lambda := by
    simpa [boundary.sourceSymbols_eq] using hn_source
  exact boundary.visibleAtomInLambdaCutoffData hn

noncomputable def globalArithmeticData
    {base : SourceObjectTheoremBasePackage}
    {data : SourceObjectConcreteCommonData base}
    {lambda : ℝ}
    (boundary :
      SourceEvaluationVisibleFinitePrimeBoundary data lambda) :
    CCM25Concrete.PrimePowerArithmetic.SourceGlobalFinitePrimeArithmeticData
      base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest where
  atIndex := by
    intro n hn
    have hn_source :
        n ∈ boundary.sourceWeilForm.toWeilFormSymbols.globalPrimeIndexSet := by
      simpa [boundary.sourceSymbols_eq] using hn
    have hvisible :
        (boundary.sourceSymbols_eq ▸
          data.concreteCommonTest).toSourceTestEvaluationInterface.sourceAtomVisible n :=
      ((boundary.globalExact n).1 hn_source).atomVisible
    exact
      transportSourceFinitePrimeArithmeticData boundary.sourceSymbols_eq
        data.concreteCommonTest
        (boundary.visibleData.toSourceEvaluationVisibleArithmeticData
          |>.visibleArithmeticData |>.atVisibleIndex n hvisible)

noncomputable def restrictedArithmeticData
    {base : SourceObjectTheoremBasePackage}
    {data : SourceObjectConcreteCommonData base}
    {lambda : ℝ}
    (boundary :
      SourceEvaluationVisibleFinitePrimeBoundary data lambda) :
    CCM25Concrete.PrimePowerArithmetic.SourceRestrictedFinitePrimeArithmeticData
      base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest lambda where
  atIndex := by
    intro n hn
    exact (boundary.visibleAtomInLambdaCutoffData hn).sourceArithmeticData

theorem pairing_formula
    {base : SourceObjectTheoremBasePackage}
    {data : SourceObjectConcreteCommonData base}
    {lambda : ℝ}
    (boundary :
      SourceEvaluationVisibleFinitePrimeBoundary data lambda)
    {n : ℕ}
    (hn :
      (boundary.sourceSymbols_eq ▸
        data.concreteCommonTest).toSourceTestEvaluationInterface.sourceAtomVisible n) :
    boundary.sourceWeilForm.toWeilFormSymbols.primePowerPairing n
      (boundary.sourceSymbols_eq ▸ data.concreteCommonTest).sourceTest
      (boundary.sourceSymbols_eq ▸ data.concreteCommonTest).sourceTest =
      (1 / Real.sqrt (n : ℝ)) *
        (boundary.sourceWeilForm.evaluation.valueAt
            (boundary.sourceAlgebra.legacy.decode
              (boundary.sourceSymbols_eq ▸
                data.concreteCommonTest).sourceConvolutionSquare)
            (CCM25Concrete.PrimePowerEvaluation.SourceForwardPoint n) +
          boundary.sourceWeilForm.evaluation.valueAt
            (boundary.sourceAlgebra.legacy.decode
              (boundary.sourceSymbols_eq ▸
                data.concreteCommonTest).sourceConvolutionSquare)
            (CCM25Concrete.PrimePowerEvaluation.SourceInversePoint n)) :=
  FixedLambdaSourceEvaluationVisibleArithmeticData.pairing_formula
    boundary.visibleData.toSourceEvaluationVisibleArithmeticData hn

end SourceEvaluationVisibleFinitePrimeBoundary

structure SourceEvaluationVisibleFinitePrimeSupportBoundary
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) where
  sourceAlgebra : AnalyticCore.SourceTestAlgebra
  sourceWeilForm : AnalyticCore.SourceWeilFormData sourceAlgebra
  sourceSymbols_eq :
    base.ccm25Model.toWeilFormSymbols = sourceWeilForm.toWeilFormSymbols
  oneLtLambda : 1 < lambda

namespace SourceEvaluationVisibleFinitePrimeSupportBoundary

noncomputable def supportData
    {base : SourceObjectTheoremBasePackage}
    {data : SourceObjectConcreteCommonData base}
    {lambda : ℝ}
    (boundary :
      SourceEvaluationVisibleFinitePrimeSupportBoundary data lambda) :
    CCM25Concrete.FinitePrimeSourceData.FixedLambdaCommonFinitePrimeSupportData
      boundary.sourceWeilForm.toWeilFormSymbols
      (boundary.sourceSymbols_eq ▸ data.concreteCommonTest) lambda :=
  SourceEvaluationVisibleFinitePrimeBoundary.supportDataOfSourceWeilForm
    data boundary.sourceWeilForm boundary.sourceSymbols_eq lambda
    boundary.oneLtLambda

noncomputable def visibleData
    {base : SourceObjectTheoremBasePackage}
    {data : SourceObjectConcreteCommonData base}
    {lambda : ℝ}
    (boundary :
      SourceEvaluationVisibleFinitePrimeSupportBoundary data lambda) :
    CCM25Concrete.FinitePrimeSourceData.FixedLambdaSourceWeilFormVisibleArithmeticData
      boundary.sourceWeilForm
      (boundary.sourceSymbols_eq ▸ data.concreteCommonTest) lambda :=
  SourceEvaluationVisibleFinitePrimeBoundary.visibleDataOfSourceWeilForm
    data boundary.sourceWeilForm boundary.sourceSymbols_eq lambda
    boundary.oneLtLambda

noncomputable def ofSourceWeilForm
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    {sourceAlgebra : AnalyticCore.SourceTestAlgebra}
    (sourceWeilForm : AnalyticCore.SourceWeilFormData sourceAlgebra)
    (sourceSymbols_eq :
      base.ccm25Model.toWeilFormSymbols =
        sourceWeilForm.toWeilFormSymbols)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    SourceEvaluationVisibleFinitePrimeSupportBoundary data lambda where
  sourceAlgebra := sourceAlgebra
  sourceWeilForm := sourceWeilForm
  sourceSymbols_eq := sourceSymbols_eq
  oneLtLambda := hlambda

noncomputable def ofFinitePrimeBoundary
    {base : SourceObjectTheoremBasePackage}
    {data : SourceObjectConcreteCommonData base}
    {lambda : ℝ}
    (boundary :
      SourceEvaluationVisibleFinitePrimeBoundary data lambda) :
    SourceEvaluationVisibleFinitePrimeSupportBoundary data lambda where
  sourceAlgebra := boundary.sourceAlgebra
  sourceWeilForm := boundary.sourceWeilForm
  sourceSymbols_eq := boundary.sourceSymbols_eq
  oneLtLambda := boundary.oneLtLambda

structure VisibleAtomInLambdaCutoffData
    {base : SourceObjectTheoremBasePackage}
    {data : SourceObjectConcreteCommonData base}
    {lambda : ℝ}
    (boundary :
      SourceEvaluationVisibleFinitePrimeSupportBoundary data lambda)
    (n : ℕ) where
  restrictedMem :
    n ∈ boundary.sourceWeilForm.toWeilFormSymbols.restrictedPrimeIndexSet
      lambda
  routeVisible :
    boundary.sourceWeilForm.toWeilFormSymbols.finitePrimeAtomVisible n
      (boundary.sourceWeilForm.toWeilFormSymbols.convolutionStar
        (boundary.sourceSymbols_eq ▸ data.concreteCommonTest).sourceTest
        (boundary.sourceSymbols_eq ▸ data.concreteCommonTest).sourceTest)
  sourceVisible :
    (boundary.sourceSymbols_eq ▸
      data.concreteCommonTest).toSourceTestEvaluationInterface.sourceAtomVisible n
  lambdaCut :
    CCM25Concrete.PrimePowerSupport.SourceLambdaCut lambda n
  restrictedIndexData :
    CCM25Concrete.PrimePowerSupport.SourceRestrictedIndexData
      boundary.sourceWeilForm.toWeilFormSymbols
      (boundary.sourceSymbols_eq ▸ data.concreteCommonTest).sourceTest
      (boundary.sourceSymbols_eq ▸ data.concreteCommonTest).sourceTest lambda n
  sourceArithmeticData :
    CCM25Concrete.PrimePowerArithmetic.SourceFinitePrimeArithmeticData
      base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest n

noncomputable def visibleAtomInLambdaCutoffData
    {base : SourceObjectTheoremBasePackage}
    {data : SourceObjectConcreteCommonData base}
    {lambda : ℝ}
    (boundary :
      SourceEvaluationVisibleFinitePrimeSupportBoundary data lambda)
    {n : ℕ}
    (hn :
      n ∈ base.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet
        lambda) :
    VisibleAtomInLambdaCutoffData boundary n := by
  have hn_source :
      n ∈ boundary.sourceWeilForm.toWeilFormSymbols.restrictedPrimeIndexSet
        lambda := by
    simpa [boundary.sourceSymbols_eq] using hn
  let hindex := boundary.supportData.restrictedIndexData n hn_source
  have hsourceVisible :
      (boundary.sourceSymbols_eq ▸
        data.concreteCommonTest).toSourceTestEvaluationInterface.sourceAtomVisible n :=
    hindex.atomVisible
  exact
    { restrictedMem := hn_source
      routeVisible := hindex.atomVisible
      sourceVisible := hsourceVisible
      lambdaCut := hindex.lambdaCut
      restrictedIndexData := hindex
      sourceArithmeticData :=
        transportSourceFinitePrimeArithmeticData boundary.sourceSymbols_eq
          data.concreteCommonTest
          (boundary.visibleData.toSourceEvaluationVisibleArithmeticData
            |>.visibleArithmeticData |>.atVisibleIndex n hsourceVisible) }

noncomputable def routeVisibleAtomInLambdaCutoffData
    {base : SourceObjectTheoremBasePackage}
    {data : SourceObjectConcreteCommonData base}
    {lambda : ℝ}
    (boundary :
      SourceEvaluationVisibleFinitePrimeSupportBoundary data lambda)
    {n : ℕ}
    (hvisible :
      base.ccm25Model.toWeilFormSymbols.finitePrimeAtomVisible n
        (base.ccm25Model.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest data.concreteCommonTest.sourceTest))
    (hOne : 1 < n)
    (hCutoff : (n : ℝ) ≤ lambda ^ 2) :
    VisibleAtomInLambdaCutoffData boundary n := by
  have hsourceVisible :
      boundary.sourceWeilForm.toWeilFormSymbols.finitePrimeAtomVisible n
        (boundary.sourceWeilForm.toWeilFormSymbols.convolutionStar
          (boundary.sourceSymbols_eq ▸ data.concreteCommonTest).sourceTest
          (boundary.sourceSymbols_eq ▸ data.concreteCommonTest).sourceTest) :=
    transport_routeFinitePrimeAtomVisible boundary.sourceSymbols_eq
      data.concreteCommonTest hvisible
  have hn_source :
      n ∈ boundary.sourceWeilForm.toWeilFormSymbols.restrictedPrimeIndexSet
        lambda :=
    boundary.supportData.routeVisibleRestrictedIndex n hsourceVisible
      hOne hCutoff
  have hn :
      n ∈ base.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet
        lambda := by
    simpa [boundary.sourceSymbols_eq] using hn_source
  exact boundary.visibleAtomInLambdaCutoffData hn

noncomputable def globalArithmeticData
    {base : SourceObjectTheoremBasePackage}
    {data : SourceObjectConcreteCommonData base}
    {lambda : ℝ}
    (boundary :
      SourceEvaluationVisibleFinitePrimeSupportBoundary data lambda) :
    CCM25Concrete.PrimePowerArithmetic.SourceGlobalFinitePrimeArithmeticData
      base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest where
  atIndex := by
    intro n hn
    have hn_source :
        n ∈ boundary.sourceWeilForm.toWeilFormSymbols.globalPrimeIndexSet := by
      simpa [boundary.sourceSymbols_eq] using hn
    have hvisible :
        (boundary.sourceSymbols_eq ▸
          data.concreteCommonTest).toSourceTestEvaluationInterface.sourceAtomVisible n :=
      (boundary.supportData.globalIndexData n hn_source).atomVisible
    exact
      transportSourceFinitePrimeArithmeticData boundary.sourceSymbols_eq
        data.concreteCommonTest
        (boundary.visibleData.toSourceEvaluationVisibleArithmeticData
          |>.visibleArithmeticData |>.atVisibleIndex n hvisible)

noncomputable def restrictedArithmeticData
    {base : SourceObjectTheoremBasePackage}
    {data : SourceObjectConcreteCommonData base}
    {lambda : ℝ}
    (boundary :
      SourceEvaluationVisibleFinitePrimeSupportBoundary data lambda) :
    CCM25Concrete.PrimePowerArithmetic.SourceRestrictedFinitePrimeArithmeticData
      base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest lambda where
  atIndex := by
    intro n hn
    exact (boundary.visibleAtomInLambdaCutoffData hn).sourceArithmeticData

theorem pairing_formula
    {base : SourceObjectTheoremBasePackage}
    {data : SourceObjectConcreteCommonData base}
    {lambda : ℝ}
    (boundary :
      SourceEvaluationVisibleFinitePrimeSupportBoundary data lambda)
    {n : ℕ}
    (hn :
      (boundary.sourceSymbols_eq ▸
        data.concreteCommonTest).toSourceTestEvaluationInterface.sourceAtomVisible n) :
    boundary.sourceWeilForm.toWeilFormSymbols.primePowerPairing n
      (boundary.sourceSymbols_eq ▸ data.concreteCommonTest).sourceTest
      (boundary.sourceSymbols_eq ▸ data.concreteCommonTest).sourceTest =
      (1 / Real.sqrt (n : ℝ)) *
        (boundary.sourceWeilForm.evaluation.valueAt
            (boundary.sourceAlgebra.legacy.decode
              (boundary.sourceSymbols_eq ▸
                data.concreteCommonTest).sourceConvolutionSquare)
            (CCM25Concrete.PrimePowerEvaluation.SourceForwardPoint n) +
          boundary.sourceWeilForm.evaluation.valueAt
            (boundary.sourceAlgebra.legacy.decode
              (boundary.sourceSymbols_eq ▸
                data.concreteCommonTest).sourceConvolutionSquare)
            (CCM25Concrete.PrimePowerEvaluation.SourceInversePoint n)) :=
  FixedLambdaSourceEvaluationVisibleArithmeticData.pairing_formula
    boundary.visibleData.toSourceEvaluationVisibleArithmeticData hn

end SourceEvaluationVisibleFinitePrimeSupportBoundary

namespace SourceEvaluationVisibleFinitePrimeBoundary

noncomputable def toSupportBoundary
    {base : SourceObjectTheoremBasePackage}
    {data : SourceObjectConcreteCommonData base}
    {lambda : ℝ}
    (boundary :
      SourceEvaluationVisibleFinitePrimeBoundary data lambda) :
    SourceEvaluationVisibleFinitePrimeSupportBoundary data lambda :=
  SourceEvaluationVisibleFinitePrimeSupportBoundary.ofFinitePrimeBoundary
    boundary

end SourceEvaluationVisibleFinitePrimeBoundary

noncomputable def commonFinitePrimeConcreteObject
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    CCM25Concrete.FinitePrimeCertificate.FixedLambdaFinitePrimeConcreteObject
      base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest lambda :=
  CCM25Concrete.FinitePrimeCertificate.concrete_object_of_arithmetic_certificate
    (data.commonArithmeticCertificate lambda hlambda)

theorem common_finite_prime_concrete_object_certificate_eq
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    (data.commonFinitePrimeConcreteObject lambda hlambda).certificate =
      data.commonArithmeticCertificate lambda hlambda :=
  rfl

theorem common_finite_prime_concrete_object_source_test_eq_concrete
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    (data.commonFinitePrimeConcreteObject lambda hlambda).sourceTest =
      data.concreteCommonTest.toSourceTestEvaluationInterface := by
  calc
    (data.commonFinitePrimeConcreteObject lambda hlambda).sourceTest =
        (data.commonArithmeticCertificate lambda hlambda).support.sourceTest :=
      rfl
    _ = data.concreteCommonTest.toSourceTestEvaluationInterface :=
      by
        simpa [commonArithmeticCertificate]
          using
            data.common_fixed_lambda_arithmetic_data_source_test_eq_concrete
              lambda hlambda

structure CommonFinitePrimeCertificateBoundary
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) where
  oneLtLambda : 1 < lambda

namespace CommonFinitePrimeCertificateBoundary

noncomputable def concreteObject
    {base : SourceObjectTheoremBasePackage}
    {data : SourceObjectConcreteCommonData base}
    {lambda : ℝ}
    (boundary : CommonFinitePrimeCertificateBoundary data lambda) :
    CCM25Concrete.FinitePrimeCertificate.FixedLambdaFinitePrimeConcreteObject
      base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest lambda :=
  data.commonFinitePrimeConcreteObject lambda boundary.oneLtLambda

def supportData
    {base : SourceObjectTheoremBasePackage}
    {data : SourceObjectConcreteCommonData base}
    {lambda : ℝ}
    (boundary : CommonFinitePrimeCertificateBoundary data lambda) :
    CCM25Concrete.FinitePrimeSourceData.FixedLambdaCommonFinitePrimeSupportData
      base.ccm25Model.toWeilFormSymbols data.concreteCommonTest lambda :=
  data.commonFixedLambdaFinitePrimeSupportData lambda boundary.oneLtLambda

noncomputable def globalArithmeticData
    {base : SourceObjectTheoremBasePackage}
    {data : SourceObjectConcreteCommonData base}
    {lambda : ℝ}
    (boundary : CommonFinitePrimeCertificateBoundary data lambda) :
    CCM25Concrete.PrimePowerArithmetic.SourceGlobalFinitePrimeArithmeticData
      base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest :=
  boundary.concreteObject.globalArithmeticData

noncomputable def restrictedArithmeticData
    {base : SourceObjectTheoremBasePackage}
    {data : SourceObjectConcreteCommonData base}
    {lambda : ℝ}
    (boundary : CommonFinitePrimeCertificateBoundary data lambda) :
    CCM25Concrete.PrimePowerArithmetic.SourceRestrictedFinitePrimeArithmeticData
      base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest lambda :=
  boundary.concreteObject.restrictedArithmeticData

end CommonFinitePrimeCertificateBoundary

theorem common_finite_prime_concrete_object_global_visible
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    {sourceAlgebra : AnalyticCore.SourceTestAlgebra}
    (sourceWeilForm : AnalyticCore.SourceWeilFormData sourceAlgebra)
    (sourceSymbols_eq :
      base.ccm25Model.toWeilFormSymbols =
        sourceWeilForm.toWeilFormSymbols)
    {n : ℕ}
    (hn : n ∈ base.ccm25Model.toWeilFormSymbols.globalPrimeIndexSet) :
    base.ccm25Model.toWeilFormSymbols.finitePrimeAtomVisible n
      (base.ccm25Model.toWeilFormSymbols.convolutionStar
        data.concreteCommonTest.sourceTest data.concreteCommonTest.sourceTest) := by
  have hsourceGlobal :
      n ∈ sourceWeilForm.toWeilFormSymbols.globalPrimeIndexSet :=
    transport_globalPrimeIndex_mem sourceSymbols_eq hn
  have hsourceVisible :
      sourceWeilForm.toWeilFormSymbols.finitePrimeAtomVisible n
        (sourceWeilForm.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) :=
    ((AnalyticCore.SourceWeilFormData.toWeilFormSymbols_globalPrimeIndex_exact
      sourceWeilForm
      (sourceWeilForm.toWeilFormSymbols.convolutionStar
        data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest) n).1 hsourceGlobal).2
  exact
    transport_finitePrimeAtomVisible_convolution sourceSymbols_eq.symm
      data.concreteCommonTest.sourceTest data.concreteCommonTest.sourceTest
      hsourceVisible

theorem common_route_visible_atom_data
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    {sourceAlgebra : AnalyticCore.SourceTestAlgebra}
    (sourceWeilForm : AnalyticCore.SourceWeilFormData sourceAlgebra)
    (sourceSymbols_eq :
      base.ccm25Model.toWeilFormSymbols =
        sourceWeilForm.toWeilFormSymbols)
    {n : ℕ}
    (hvisible :
      base.ccm25Model.toWeilFormSymbols.finitePrimeAtomVisible n
        (base.ccm25Model.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest)) :
    CCM25Concrete.PrimePowerSupport.SourceVisibleAtomData
      base.ccm25Model.toWeilFormSymbols
      data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest n := by
  have hsourceVisible :
      sourceWeilForm.toWeilFormSymbols.finitePrimeAtomVisible n
        (sourceWeilForm.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) :=
    transport_finitePrimeAtomVisible_convolution sourceSymbols_eq
      data.concreteCommonTest.sourceTest data.concreteCommonTest.sourceTest
      hvisible
  have hprime : IsPrimePow n :=
    AnalyticCore.SourceWeilFormData.toWeilFormSymbols_finitePrimeAtomVisible_primePower
      sourceWeilForm
      (sourceWeilForm.toWeilFormSymbols.convolutionStar
        data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest)
      hsourceVisible
  exact
    { primePowerIndex := hprime
      atomVisible := hvisible }

theorem common_finite_prime_concrete_object_global_index_data
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    {sourceAlgebra : AnalyticCore.SourceTestAlgebra}
    (sourceWeilForm : AnalyticCore.SourceWeilFormData sourceAlgebra)
    (sourceSymbols_eq :
      base.ccm25Model.toWeilFormSymbols =
        sourceWeilForm.toWeilFormSymbols)
    {n : ℕ}
    (hn : n ∈ base.ccm25Model.toWeilFormSymbols.globalPrimeIndexSet) :
    CCM25Concrete.PrimePowerSupport.SourceGlobalIndexData
      base.ccm25Model.toWeilFormSymbols
      data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest n where
  primePowerIndex := by
    have hsourceGlobal :
        n ∈ sourceWeilForm.toWeilFormSymbols.globalPrimeIndexSet :=
      transport_globalPrimeIndex_mem sourceSymbols_eq hn
    exact
      ((AnalyticCore.SourceWeilFormData.toWeilFormSymbols_globalPrimeIndex_exact
        sourceWeilForm
        (sourceWeilForm.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) n).1 hsourceGlobal).1
  atomVisible :=
    data.common_finite_prime_concrete_object_global_visible
      sourceWeilForm sourceSymbols_eq hn

theorem common_finite_prime_concrete_object_restricted_visible
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    {sourceAlgebra : AnalyticCore.SourceTestAlgebra}
    (sourceWeilForm : AnalyticCore.SourceWeilFormData sourceAlgebra)
    (sourceSymbols_eq :
      base.ccm25Model.toWeilFormSymbols =
        sourceWeilForm.toWeilFormSymbols)
    (lambda : ℝ) (_hlambda : 1 < lambda)
    {n : ℕ}
    (hn : n ∈ base.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet
      lambda) :
    base.ccm25Model.toWeilFormSymbols.finitePrimeAtomVisible n
      (base.ccm25Model.toWeilFormSymbols.convolutionStar
        data.concreteCommonTest.sourceTest data.concreteCommonTest.sourceTest) := by
  have hsourceRestricted :
      n ∈ sourceWeilForm.toWeilFormSymbols.restrictedPrimeIndexSet lambda :=
    transport_restrictedPrimeIndex_mem sourceSymbols_eq lambda hn
  have hsourceVisible :
      sourceWeilForm.toWeilFormSymbols.finitePrimeAtomVisible n
        (sourceWeilForm.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) :=
    (((AnalyticCore.SourceWeilFormData.toWeilFormSymbols_restrictedPrimeIndex_exact
      sourceWeilForm lambda
      (sourceWeilForm.toWeilFormSymbols.convolutionStar
        data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest) n).1 hsourceRestricted).2).1
  exact
    transport_finitePrimeAtomVisible_convolution sourceSymbols_eq.symm
      data.concreteCommonTest.sourceTest data.concreteCommonTest.sourceTest
      hsourceVisible

theorem common_finite_prime_concrete_object_restricted_index_data
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    {sourceAlgebra : AnalyticCore.SourceTestAlgebra}
    (sourceWeilForm : AnalyticCore.SourceWeilFormData sourceAlgebra)
    (sourceSymbols_eq :
      base.ccm25Model.toWeilFormSymbols =
        sourceWeilForm.toWeilFormSymbols)
    (lambda : ℝ) (hlambda : 1 < lambda)
    {n : ℕ}
    (hn : n ∈ base.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet
      lambda) :
    CCM25Concrete.PrimePowerSupport.SourceRestrictedIndexData
      base.ccm25Model.toWeilFormSymbols
      data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest lambda n where
  primePowerIndex := by
    have hsourceRestricted :
        n ∈ sourceWeilForm.toWeilFormSymbols.restrictedPrimeIndexSet lambda :=
      transport_restrictedPrimeIndex_mem sourceSymbols_eq lambda hn
    exact
      ((AnalyticCore.SourceWeilFormData.toWeilFormSymbols_restrictedPrimeIndex_exact
        sourceWeilForm lambda
        (sourceWeilForm.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) n).1 hsourceRestricted).1
  atomVisible :=
    data.common_finite_prime_concrete_object_restricted_visible
      sourceWeilForm sourceSymbols_eq lambda hlambda hn
  lambdaCut := by
    have hsourceRestricted :
        n ∈ sourceWeilForm.toWeilFormSymbols.restrictedPrimeIndexSet lambda :=
      transport_restrictedPrimeIndex_mem sourceSymbols_eq lambda hn
    exact
      (((AnalyticCore.SourceWeilFormData.toWeilFormSymbols_restrictedPrimeIndex_exact
        sourceWeilForm lambda
        (sourceWeilForm.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) n).1 hsourceRestricted).2).2

theorem common_finite_prime_concrete_object_restricted_index_one_lt
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    {sourceAlgebra : AnalyticCore.SourceTestAlgebra}
    (sourceWeilForm : AnalyticCore.SourceWeilFormData sourceAlgebra)
    (sourceSymbols_eq :
      base.ccm25Model.toWeilFormSymbols =
        sourceWeilForm.toWeilFormSymbols)
    (lambda : ℝ) (hlambda : 1 < lambda)
    {n : ℕ}
    (hn : n ∈ base.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet
      lambda) :
    1 < n :=
  (data.common_finite_prime_concrete_object_restricted_index_data
    sourceWeilForm sourceSymbols_eq lambda hlambda hn).lambdaCut.1

theorem common_finite_prime_concrete_object_restricted_index_le_lambda_sq
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    {sourceAlgebra : AnalyticCore.SourceTestAlgebra}
    (sourceWeilForm : AnalyticCore.SourceWeilFormData sourceAlgebra)
    (sourceSymbols_eq :
      base.ccm25Model.toWeilFormSymbols =
        sourceWeilForm.toWeilFormSymbols)
    (lambda : ℝ) (hlambda : 1 < lambda)
    {n : ℕ}
    (hn : n ∈ base.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet
      lambda) :
    (n : ℝ) ≤ lambda ^ 2 :=
  (data.common_finite_prime_concrete_object_restricted_index_data
    sourceWeilForm sourceSymbols_eq lambda hlambda hn).lambdaCut.2

theorem common_finite_prime_visibility_at_lambda
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    {sourceAlgebra : AnalyticCore.SourceTestAlgebra}
    (sourceWeilForm : AnalyticCore.SourceWeilFormData sourceAlgebra)
    (sourceSymbols_eq :
      base.ccm25Model.toWeilFormSymbols =
        sourceWeilForm.toWeilFormSymbols)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    CCM25Concrete.FinitePrimeExact.FinitePrimeVisibilityAtLambdaStatement
      base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest lambda := by
  constructor
  · intro n hvisible
    have hsourceVisible :
        sourceWeilForm.toWeilFormSymbols.finitePrimeAtomVisible n
          (sourceWeilForm.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) :=
      transport_finitePrimeAtomVisible_convolution sourceSymbols_eq
        data.concreteCommonTest.sourceTest data.concreteCommonTest.sourceTest
        hvisible
    have hsourcePrime : IsPrimePow n :=
      AnalyticCore.SourceWeilFormData.toWeilFormSymbols_finitePrimeAtomVisible_primePower
        sourceWeilForm
        (sourceWeilForm.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest)
        hsourceVisible
    have hsourceGlobal :
        n ∈ sourceWeilForm.toWeilFormSymbols.globalPrimeIndexSet :=
      AnalyticCore.SourceWeilFormData.toWeilFormSymbols_globalPrimeIndex_mem_of_primePower_visible
        sourceWeilForm
        (sourceWeilForm.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest)
        hsourcePrime hsourceVisible
    exact transport_globalPrimeIndex_mem sourceSymbols_eq.symm hsourceGlobal
  · constructor
    · intro n hvisible hOne hCutoff
      have hsourceVisible :
          sourceWeilForm.toWeilFormSymbols.finitePrimeAtomVisible n
            (sourceWeilForm.toWeilFormSymbols.convolutionStar
              data.concreteCommonTest.sourceTest
              data.concreteCommonTest.sourceTest) :=
        transport_finitePrimeAtomVisible_convolution sourceSymbols_eq
          data.concreteCommonTest.sourceTest data.concreteCommonTest.sourceTest
          hvisible
      have hsourceRestricted :
          n ∈ sourceWeilForm.toWeilFormSymbols.restrictedPrimeIndexSet
            lambda :=
        AnalyticCore.SourceWeilFormData.toWeilFormSymbols_restrictedPrimeIndex_mem_of_visible
          sourceWeilForm lambda hlambda
          (sourceWeilForm.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest)
          hsourceVisible hOne hCutoff
      exact
        transport_restrictedPrimeIndex_mem sourceSymbols_eq.symm lambda
          hsourceRestricted
    · intro n
      exact
        transport_finitePrimeTerm_normalization sourceSymbols_eq
          data.concreteCommonTest.sourceTest data.concreteCommonTest.sourceTest n
          (AnalyticCore.SourceWeilFormData.toWeilFormSymbols_finitePrimeTerm_convolutionStar
            sourceWeilForm data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest n)

theorem common_finite_prime_visibility_statement
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    WeilFormSymbols.FinitePrimeVisibilityStatement
      base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest :=
  (CCM25Concrete.FinitePrimeInterface.finite_prime_normalization_of_common_source_test_certificates
    (CCM25Concrete.FinitePrimeSourceData.fixedLambdaArithmeticSourceTestCertificatesForAllTests
      data.commonFinitePrimeArithmeticSourceDataOwner))
    data.concreteCommonTest.sourceTest data.concreteCommonTest.sourceTest

theorem common_finite_prime_global_coverage_statement
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    WeilFormSymbols.GlobalPrimeIndexCoverageStatement
      base.ccm25Model.toWeilFormSymbols
      (base.ccm25Model.toWeilFormSymbols.convolutionStar
        data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest) :=
  (CCM25Concrete.FinitePrimeInterface.finite_prime_visibility_of_common_source_test_certificates
    ((CCM25Concrete.FinitePrimeSourceData.fixedLambdaArithmeticSourceTestCertificatesForAllTests
      data.commonFinitePrimeArithmeticSourceDataOwner)
        data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest)).globalPrimeIndexCoverage

theorem common_finite_prime_restricted_coverage_statement
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    ∀ lambda : ℝ,
      1 < lambda →
        WeilFormSymbols.RestrictedPrimeIndexCoverageStatement
          base.ccm25Model.toWeilFormSymbols lambda
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) := by
  intro lambda hlambda
  exact
    (CCM25Concrete.FinitePrimeInterface.finite_prime_visibility_of_common_source_test_certificates
      ((CCM25Concrete.FinitePrimeSourceData.fixedLambdaArithmeticSourceTestCertificatesForAllTests
        data.commonFinitePrimeArithmeticSourceDataOwner)
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest)).restrictedPrimeIndexCoverage
        lambda hlambda

theorem common_finite_prime_term_normalization_statement
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    WeilFormSymbols.FinitePrimeTermNormalizationStatement
      base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest :=
  CCM25Concrete.FinitePrimeInterface.finite_prime_term_normalization_of_common_source_test_certificates
    ((CCM25Concrete.FinitePrimeSourceData.fixedLambdaArithmeticSourceTestCertificatesForAllTests
      data.commonFinitePrimeArithmeticSourceDataOwner)
        data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest)

theorem common_global_finite_prime_term_sum_read_off
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    {sourceAlgebra : AnalyticCore.SourceTestAlgebra}
    (sourceWeilForm : AnalyticCore.SourceWeilFormData sourceAlgebra)
    (sourceSymbols_eq :
      base.ccm25Model.toWeilFormSymbols =
        sourceWeilForm.toWeilFormSymbols) :
    (∑ n ∈ base.ccm25Model.toWeilFormSymbols.globalPrimeIndexSet,
      base.ccm25Model.toWeilFormSymbols.finitePrimeTerm n
        (base.ccm25Model.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest)) =
      ∑ n ∈ base.ccm25Model.toWeilFormSymbols.globalPrimeIndexSet,
        base.ccm25Model.toWeilFormSymbols.vonMangoldtWeight n *
          base.ccm25Model.toWeilFormSymbols.primePowerPairing n
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest := by
  apply Finset.sum_congr rfl
  intro n _hn
  exact
    transport_finitePrimeTerm_normalization sourceSymbols_eq
      data.concreteCommonTest.sourceTest data.concreteCommonTest.sourceTest n
      (AnalyticCore.SourceWeilFormData.toWeilFormSymbols_finitePrimeTerm_convolutionStar
        sourceWeilForm data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest n)

theorem common_global_finite_prime_term_sum_read_off_of_certificate_owner
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    (∑ n ∈ base.ccm25Model.toWeilFormSymbols.globalPrimeIndexSet,
      base.ccm25Model.toWeilFormSymbols.finitePrimeTerm n
        (base.ccm25Model.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest)) =
      ∑ n ∈ base.ccm25Model.toWeilFormSymbols.globalPrimeIndexSet,
        base.ccm25Model.toWeilFormSymbols.vonMangoldtWeight n *
          base.ccm25Model.toWeilFormSymbols.primePowerPairing n
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest := by
  apply Finset.sum_congr rfl
  intro n _hn
  exact data.common_finite_prime_term_normalization_statement n

theorem common_global_von_mangoldt_pairing_sum_read_off_of_support_boundary
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ)
    (boundary :
      SourceEvaluationVisibleFinitePrimeSupportBoundary data lambda) :
    (∑ n ∈ base.ccm25Model.toWeilFormSymbols.globalPrimeIndexSet,
      base.ccm25Model.toWeilFormSymbols.vonMangoldtWeight n *
        base.ccm25Model.toWeilFormSymbols.primePowerPairing n
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) =
      PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
        base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest
        boundary.globalArithmeticData := by
  calc
    (∑ n ∈ base.ccm25Model.toWeilFormSymbols.globalPrimeIndexSet,
      base.ccm25Model.toWeilFormSymbols.vonMangoldtWeight n *
        base.ccm25Model.toWeilFormSymbols.primePowerPairing n
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) =
        PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSumOnIndexSet
          base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest boundary.globalArithmeticData :=
      PrimePowerArithmetic.source_von_mangoldt_pairing_sum_on_index_set_formula_source_evaluations
        boundary.globalArithmeticData
    _ =
        PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
          base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest boundary.globalArithmeticData :=
      PrimePowerArithmetic.source_global_finite_prime_evaluator_sum_on_index_set_eq_mathlib
        boundary.globalArithmeticData

theorem common_global_von_mangoldt_pairing_sum_read_off_of_certificate_boundary
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ)
    (boundary : CommonFinitePrimeCertificateBoundary data lambda) :
    (∑ n ∈ base.ccm25Model.toWeilFormSymbols.globalPrimeIndexSet,
      base.ccm25Model.toWeilFormSymbols.vonMangoldtWeight n *
        base.ccm25Model.toWeilFormSymbols.primePowerPairing n
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) =
      PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
        base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest
        boundary.globalArithmeticData := by
  calc
    (∑ n ∈ base.ccm25Model.toWeilFormSymbols.globalPrimeIndexSet,
      base.ccm25Model.toWeilFormSymbols.vonMangoldtWeight n *
        base.ccm25Model.toWeilFormSymbols.primePowerPairing n
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) =
        PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSumOnIndexSet
          base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest
          boundary.globalArithmeticData :=
      PrimePowerArithmetic.source_von_mangoldt_pairing_sum_on_index_set_formula_source_evaluations
        boundary.globalArithmeticData
    _ =
        PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
          base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest
          boundary.globalArithmeticData :=
      PrimePowerArithmetic.source_global_finite_prime_evaluator_sum_on_index_set_eq_mathlib
        boundary.globalArithmeticData

theorem common_global_von_mangoldt_pairing_sum_read_off
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ)
    (boundary : SourceEvaluationVisibleFinitePrimeBoundary data lambda) :
    (∑ n ∈ base.ccm25Model.toWeilFormSymbols.globalPrimeIndexSet,
      base.ccm25Model.toWeilFormSymbols.vonMangoldtWeight n *
        base.ccm25Model.toWeilFormSymbols.primePowerPairing n
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) =
      PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
        base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest
        boundary.globalArithmeticData := by
  simpa [SourceEvaluationVisibleFinitePrimeBoundary.globalArithmeticData,
    SourceEvaluationVisibleFinitePrimeSupportBoundary.globalArithmeticData,
    SourceEvaluationVisibleFinitePrimeSupportBoundary.ofFinitePrimeBoundary,
    SourceEvaluationVisibleFinitePrimeBoundary.toSupportBoundary] using
      data.common_global_von_mangoldt_pairing_sum_read_off_of_support_boundary
        lambda boundary.toSupportBoundary

theorem common_psi_scoped_source_evaluator_read_off
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ)
    (boundary : SourceEvaluationVisibleFinitePrimeBoundary data lambda) :
    base.ccm25Model.toWeilFormSymbols.psi
        (base.ccm25Model.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) =
      base.ccm25Model.toWeilFormSymbols.poleFunctional
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
        base.ccm25Model.toWeilFormSymbols.archimedeanTerm
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
          PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
            base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest boundary.globalArithmeticData := by
  calc
    base.ccm25Model.toWeilFormSymbols.psi
        (base.ccm25Model.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) =
      base.ccm25Model.toWeilFormSymbols.poleFunctional
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
        base.ccm25Model.toWeilFormSymbols.archimedeanTerm
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
          (∑ n ∈ base.ccm25Model.toWeilFormSymbols.globalPrimeIndexSet,
            base.ccm25Model.toWeilFormSymbols.finitePrimeTerm n
              (base.ccm25Model.toWeilFormSymbols.convolutionStar
                data.concreteCommonTest.sourceTest
                data.concreteCommonTest.sourceTest)) := by
      simpa [boundary.sourceSymbols_eq] using
        (AnalyticCore.SourceWeilFormData.psi_sign_statement
          boundary.sourceWeilForm
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest))
    _ =
      base.ccm25Model.toWeilFormSymbols.poleFunctional
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
        base.ccm25Model.toWeilFormSymbols.archimedeanTerm
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
          (∑ n ∈ base.ccm25Model.toWeilFormSymbols.globalPrimeIndexSet,
            base.ccm25Model.toWeilFormSymbols.vonMangoldtWeight n *
              base.ccm25Model.toWeilFormSymbols.primePowerPairing n
                data.concreteCommonTest.sourceTest
                data.concreteCommonTest.sourceTest) := by
      rw [data.common_global_finite_prime_term_sum_read_off
        boundary.sourceWeilForm boundary.sourceSymbols_eq]
    _ =
      base.ccm25Model.toWeilFormSymbols.poleFunctional
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
        base.ccm25Model.toWeilFormSymbols.archimedeanTerm
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
          PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
            base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest boundary.globalArithmeticData := by
      rw [data.common_global_von_mangoldt_pairing_sum_read_off lambda boundary]

theorem common_qw_scoped_source_evaluator_read_off
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ)
    (boundary : SourceEvaluationVisibleFinitePrimeBoundary data lambda) :
    base.ccm25Model.toWeilFormSymbols.qw
        data.concreteCommonTest.sourceTest data.concreteCommonTest.sourceTest =
      base.ccm25Model.toWeilFormSymbols.poleFunctional
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
        base.ccm25Model.toWeilFormSymbols.archimedeanTerm
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
          PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
            base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest boundary.globalArithmeticData := by
  calc
    base.ccm25Model.toWeilFormSymbols.qw
        data.concreteCommonTest.sourceTest data.concreteCommonTest.sourceTest =
      base.ccm25Model.toWeilFormSymbols.psi
        (base.ccm25Model.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) := by
      simpa [boundary.sourceSymbols_eq] using
        (AnalyticCore.SourceWeilFormData.qw_definition_statement
          boundary.sourceWeilForm data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest)
    _ =
      base.ccm25Model.toWeilFormSymbols.poleFunctional
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
        base.ccm25Model.toWeilFormSymbols.archimedeanTerm
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
          PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
            base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest boundary.globalArithmeticData :=
      data.common_psi_scoped_source_evaluator_read_off lambda boundary

theorem common_psi_scoped_source_evaluator_read_off_of_certificate_boundary
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ)
    (boundary : CommonFinitePrimeCertificateBoundary data lambda) :
    base.ccm25Model.toWeilFormSymbols.psi
        (base.ccm25Model.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) =
      base.ccm25Model.toWeilFormSymbols.poleFunctional
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
        base.ccm25Model.toWeilFormSymbols.archimedeanTerm
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
          PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
            base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest boundary.globalArithmeticData := by
  calc
    base.ccm25Model.toWeilFormSymbols.psi
        (base.ccm25Model.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) =
      base.ccm25Model.toWeilFormSymbols.poleFunctional
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
        base.ccm25Model.toWeilFormSymbols.archimedeanTerm
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
          (∑ n ∈ base.ccm25Model.toWeilFormSymbols.globalPrimeIndexSet,
            base.ccm25Model.toWeilFormSymbols.finitePrimeTerm n
              (base.ccm25Model.toWeilFormSymbols.convolutionStar
                data.concreteCommonTest.sourceTest
                data.concreteCommonTest.sourceTest)) := by
      exact
        ccm25_source_psi_sign base.ccm25Model
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest)
    _ =
      base.ccm25Model.toWeilFormSymbols.poleFunctional
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
        base.ccm25Model.toWeilFormSymbols.archimedeanTerm
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
          (∑ n ∈ base.ccm25Model.toWeilFormSymbols.globalPrimeIndexSet,
            base.ccm25Model.toWeilFormSymbols.vonMangoldtWeight n *
              base.ccm25Model.toWeilFormSymbols.primePowerPairing n
                data.concreteCommonTest.sourceTest
                data.concreteCommonTest.sourceTest) := by
      rw [data.common_global_finite_prime_term_sum_read_off_of_certificate_owner]
    _ =
      base.ccm25Model.toWeilFormSymbols.poleFunctional
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
        base.ccm25Model.toWeilFormSymbols.archimedeanTerm
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
          PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
            base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest boundary.globalArithmeticData := by
      rw [data.common_global_von_mangoldt_pairing_sum_read_off_of_certificate_boundary
        lambda boundary]

theorem common_qw_scoped_source_evaluator_read_off_of_certificate_boundary
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ)
    (boundary : CommonFinitePrimeCertificateBoundary data lambda) :
    base.ccm25Model.toWeilFormSymbols.qw
        data.concreteCommonTest.sourceTest data.concreteCommonTest.sourceTest =
      base.ccm25Model.toWeilFormSymbols.poleFunctional
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
        base.ccm25Model.toWeilFormSymbols.archimedeanTerm
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
          PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
            base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest boundary.globalArithmeticData := by
  calc
    base.ccm25Model.toWeilFormSymbols.qw
        data.concreteCommonTest.sourceTest data.concreteCommonTest.sourceTest =
      base.ccm25Model.toWeilFormSymbols.psi
        (base.ccm25Model.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) := by
      exact
        ccm25_source_qw_definition base.ccm25Model
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest
    _ =
      base.ccm25Model.toWeilFormSymbols.poleFunctional
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
        base.ccm25Model.toWeilFormSymbols.archimedeanTerm
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
          PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
            base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest boundary.globalArithmeticData :=
      data.common_psi_scoped_source_evaluator_read_off_of_certificate_boundary
        lambda boundary

theorem restricted_certificate_boundary_formula_eq_global_formula_of_concrete_common
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ)
    (boundary : CommonFinitePrimeCertificateBoundary data lambda) :
    base.ccm25Model.toWeilFormSymbols.archimedeanTerm
        (base.ccm25Model.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) +
        base.ccm25Model.toWeilFormSymbols.polePairing
          data.concreteCommonTest.sourceTest -
          CCM25Concrete.PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
            base.ccm25Model.toWeilFormSymbols
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest lambda
            boundary.restrictedArithmeticData =
      base.ccm25Model.toWeilFormSymbols.poleFunctional
        (base.ccm25Model.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) -
        base.ccm25Model.toWeilFormSymbols.archimedeanTerm
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
          CCM25Concrete.PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
            base.ccm25Model.toWeilFormSymbols
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest
            boundary.globalArithmeticData := by
  exact
    data.commonFinitePrimeArithmeticSourceData_scopedArchimedeanContributionBalance
      lambda boundary.globalArithmeticData boundary.restrictedArithmeticData

theorem restricted_boundary_formula_eq_global_formula_of_concrete_common
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ)
    (boundary : SourceEvaluationVisibleFinitePrimeBoundary data lambda) :
    base.ccm25Model.toWeilFormSymbols.archimedeanTerm
        (base.ccm25Model.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) +
        base.ccm25Model.toWeilFormSymbols.polePairing
          data.concreteCommonTest.sourceTest -
          CCM25Concrete.PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
            base.ccm25Model.toWeilFormSymbols
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest lambda
            boundary.restrictedArithmeticData =
      base.ccm25Model.toWeilFormSymbols.poleFunctional
        (base.ccm25Model.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) -
        base.ccm25Model.toWeilFormSymbols.archimedeanTerm
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
          CCM25Concrete.PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
            base.ccm25Model.toWeilFormSymbols
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest
            boundary.globalArithmeticData :=
  by
    exact
      data.commonFinitePrimeArithmeticSourceData_scopedArchimedeanContributionBalance
        lambda boundary.globalArithmeticData boundary.restrictedArithmeticData

theorem common_restricted_finite_prime_term_sum_read_off
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    {sourceAlgebra : AnalyticCore.SourceTestAlgebra}
    (sourceWeilForm : AnalyticCore.SourceWeilFormData sourceAlgebra)
    (sourceSymbols_eq :
      base.ccm25Model.toWeilFormSymbols =
        sourceWeilForm.toWeilFormSymbols)
    (lambda : ℝ) :
    (∑ n ∈ base.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet lambda,
      base.ccm25Model.toWeilFormSymbols.finitePrimeTerm n
        (base.ccm25Model.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest)) =
      ∑ n ∈ base.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet lambda,
        base.ccm25Model.toWeilFormSymbols.vonMangoldtWeight n *
          base.ccm25Model.toWeilFormSymbols.primePowerPairing n
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest := by
  apply Finset.sum_congr rfl
  intro n _hn
  exact
    transport_finitePrimeTerm_normalization sourceSymbols_eq
      data.concreteCommonTest.sourceTest data.concreteCommonTest.sourceTest n
      (AnalyticCore.SourceWeilFormData.toWeilFormSymbols_finitePrimeTerm_convolutionStar
        sourceWeilForm data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest n)

theorem common_restricted_finite_prime_term_sum_read_off_of_certificate_owner
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ) :
    (∑ n ∈ base.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet lambda,
      base.ccm25Model.toWeilFormSymbols.finitePrimeTerm n
        (base.ccm25Model.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest)) =
      ∑ n ∈ base.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet lambda,
        base.ccm25Model.toWeilFormSymbols.vonMangoldtWeight n *
          base.ccm25Model.toWeilFormSymbols.primePowerPairing n
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest := by
  apply Finset.sum_congr rfl
  intro n _hn
  exact data.common_finite_prime_term_normalization_statement n

theorem common_restricted_von_mangoldt_pairing_sum_read_off_of_support_boundary
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ)
    (boundary :
      SourceEvaluationVisibleFinitePrimeSupportBoundary data lambda) :
    (∑ n ∈ base.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet lambda,
      base.ccm25Model.toWeilFormSymbols.vonMangoldtWeight n *
        base.ccm25Model.toWeilFormSymbols.primePowerPairing n
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) =
      PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
        base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest lambda
        boundary.restrictedArithmeticData := by
  calc
    (∑ n ∈ base.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet lambda,
      base.ccm25Model.toWeilFormSymbols.vonMangoldtWeight n *
        base.ccm25Model.toWeilFormSymbols.primePowerPairing n
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) =
        PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSumOnIndexSet
          base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest lambda
          boundary.restrictedArithmeticData :=
      PrimePowerArithmetic.source_von_mangoldt_pairing_sum_on_index_set_formula_source_evaluations
        boundary.restrictedArithmeticData
    _ =
        PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
          base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest lambda
          boundary.restrictedArithmeticData :=
      PrimePowerArithmetic.source_restricted_finite_prime_evaluator_sum_on_index_set_eq_mathlib
        boundary.restrictedArithmeticData

theorem common_restricted_von_mangoldt_pairing_sum_read_off_of_certificate_boundary
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ)
    (boundary : CommonFinitePrimeCertificateBoundary data lambda) :
    (∑ n ∈ base.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet lambda,
      base.ccm25Model.toWeilFormSymbols.vonMangoldtWeight n *
        base.ccm25Model.toWeilFormSymbols.primePowerPairing n
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) =
      PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
        base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest lambda
        boundary.restrictedArithmeticData := by
  calc
    (∑ n ∈ base.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet lambda,
      base.ccm25Model.toWeilFormSymbols.vonMangoldtWeight n *
        base.ccm25Model.toWeilFormSymbols.primePowerPairing n
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) =
        PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSumOnIndexSet
          base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest lambda
          boundary.restrictedArithmeticData :=
      PrimePowerArithmetic.source_von_mangoldt_pairing_sum_on_index_set_formula_source_evaluations
        boundary.restrictedArithmeticData
    _ =
        PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
          base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest lambda
          boundary.restrictedArithmeticData :=
      PrimePowerArithmetic.source_restricted_finite_prime_evaluator_sum_on_index_set_eq_mathlib
        boundary.restrictedArithmeticData

theorem common_restricted_von_mangoldt_pairing_sum_read_off
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ)
    (boundary : SourceEvaluationVisibleFinitePrimeBoundary data lambda) :
    (∑ n ∈ base.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet lambda,
      base.ccm25Model.toWeilFormSymbols.vonMangoldtWeight n *
        base.ccm25Model.toWeilFormSymbols.primePowerPairing n
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) =
      PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
        base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
        data.concreteCommonTest.sourceTest lambda
        boundary.restrictedArithmeticData := by
  simpa [SourceEvaluationVisibleFinitePrimeBoundary.restrictedArithmeticData,
    SourceEvaluationVisibleFinitePrimeSupportBoundary.restrictedArithmeticData,
    SourceEvaluationVisibleFinitePrimeSupportBoundary.ofFinitePrimeBoundary,
    SourceEvaluationVisibleFinitePrimeBoundary.toSupportBoundary] using
      data.common_restricted_von_mangoldt_pairing_sum_read_off_of_support_boundary
        lambda boundary.toSupportBoundary

theorem ccm25_source_test_eq_arithmetic_rows
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    (data.toSourceObjectCommonData).commonTest.ccm25SourceTest =
      CCM25Concrete.Rows.source_test_of_arithmetic_rows
        (data.toSourceObjectCommonData).concreteArithmeticRows
        (data.toSourceObjectCommonData).commonTest.sourceTest
        (data.toSourceObjectCommonData).commonTest.sourceTest :=
  (data.toSourceObjectCommonData).ccm25Test_eq_commonTest

def commonFinitePrimeArithmeticSourceData
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
      base.ccm25Model.toWeilFormSymbols :=
  data.commonFinitePrimeArithmeticSourceDataOwner

theorem restricted_formula_eq_global_formula_of_concrete_common
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base)
    (lambda : ℝ)
    (pkg : CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
      base.ccm25Model.toWeilFormSymbols
      data.concreteCommonTest.sourceTest lambda) :
    base.ccm25Model.toWeilFormSymbols.archimedeanTerm
        (base.ccm25Model.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) +
        base.ccm25Model.toWeilFormSymbols.polePairing
          data.concreteCommonTest.sourceTest -
          CCM25Concrete.Package.source_restricted_finite_prime_evaluator_scoped_sum
            pkg =
      base.ccm25Model.toWeilFormSymbols.poleFunctional
        (base.ccm25Model.toWeilFormSymbols.convolutionStar
          data.concreteCommonTest.sourceTest
          data.concreteCommonTest.sourceTest) -
        base.ccm25Model.toWeilFormSymbols.archimedeanTerm
          (base.ccm25Model.toWeilFormSymbols.convolutionStar
            data.concreteCommonTest.sourceTest
            data.concreteCommonTest.sourceTest) -
          CCM25Concrete.Package.source_global_finite_prime_evaluator_scoped_sum
            pkg :=
  by
    simpa [CCM25Concrete.Package.ScopedArchimedeanContributionBalance,
      CCM25Concrete.Package.ScopedRestrictedArchimedeanFormula,
      CCM25Concrete.Package.ScopedGlobalArchimedeanFormula,
      CCM25Concrete.FinitePrimeSourceData.SourceScopedArchimedeanContributionBalance,
      CCM25Concrete.FinitePrimeSourceData.SourceScopedRestrictedArchimedeanFormula,
      CCM25Concrete.FinitePrimeSourceData.SourceScopedGlobalArchimedeanFormula]
      using
        data.commonFinitePrimeArithmeticSourceData_scopedArchimedeanContributionBalance
          lambda
          (CCM25Concrete.FinitePrimeCertificate.arithmetic_data_on_global_index_set_of_certificate
            (CCM25Concrete.Package.formula_components pkg).commonCertificate)
          (CCM25Concrete.FinitePrimeCertificate.arithmetic_data_on_restricted_index_set_of_certificate
            (CCM25Concrete.Package.formula_components pkg).commonCertificate)

theorem common_finite_prime_normalization
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    WeilFormSymbols.FinitePrimeNormalizationStatement
      base.ccm25Model.toWeilFormSymbols :=
  CCM25Concrete.FinitePrimeInterface.finite_prime_normalization_of_common_source_test_certificates
    (CCM25Concrete.FinitePrimeSourceData.fixedLambdaArithmeticSourceTestCertificatesForAllTests
      data.commonFinitePrimeArithmeticSourceDataOwner)

theorem common_finite_prime_term_normalization
    {base : SourceObjectTheoremBasePackage}
    (data : SourceObjectConcreteCommonData base) :
    WeilFormSymbols.FinitePrimeTermNormalizationStatement
      base.ccm25Model.toWeilFormSymbols data.concreteCommonTest.sourceTest
      data.concreteCommonTest.sourceTest :=
  (data.common_finite_prime_normalization
    data.concreteCommonTest.sourceTest
    data.concreteCommonTest.sourceTest).finitePrimeTermNormalization

end SourceObjectConcreteCommonData

namespace SourceObjectCommonData

def toCCM25WeilObjectPackage
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    SourceObject.CCM25WeilObjectPackage where
  weilSymbols := base.ccm25Model.toWeilFormSymbols
  concreteArithmeticRows := common.concreteArithmeticRows

theorem ccm25_source_test_eq_arithmetic_rows
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    common.commonTest.ccm25SourceTest =
      CCM25Concrete.Rows.source_test_of_arithmetic_rows
        common.concreteArithmeticRows
        common.commonTest.sourceTest common.commonTest.sourceTest :=
  common.ccm25Test_eq_commonTest

theorem finite_prime_normalization
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    WeilFormSymbols.FinitePrimeNormalizationStatement
      base.ccm25Model.toWeilFormSymbols :=
  CCM25Concrete.FinitePrimeInterface.finite_prime_normalization_of_common_source_test_certificates
    (CCM25Concrete.FinitePrimeSourceData.fixedLambdaArithmeticSourceTestCertificatesForAllTests
      common.commonFinitePrimeArithmeticSourceDataOwner)

theorem finite_prime_term_normalization
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    WeilFormSymbols.FinitePrimeTermNormalizationStatement
      base.ccm25Model.toWeilFormSymbols common.commonTest.sourceTest
      common.commonTest.sourceTest :=
  (common.finite_prime_normalization common.commonTest.sourceTest
    common.commonTest.sourceTest).finitePrimeTermNormalization

def toFinitePrimeTheoremBase
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    CCM25TheoremBaseFinitePrime where
  weilSymbols := base.ccm25Model.toWeilFormSymbols
  finitePrimeArithmeticSourceTestCertificates :=
    CCM25Concrete.FinitePrimeSourceData.fixedLambdaArithmeticSourceTestCertificatesForAllTests
      common.commonFinitePrimeArithmeticSourceDataOwner
  finitePrimeNormalization := common.finite_prime_normalization

def toPartialQWFinitePrime
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    CCM25TheoremBasePartialQWFinitePrime where
  sourceModel := base.ccm25Model
  finitePrimeArithmeticSourceTestCertificates :=
    CCM25Concrete.FinitePrimeSourceData.fixedLambdaArithmeticSourceTestCertificatesForAllTests
      common.commonFinitePrimeArithmeticSourceDataOwner
  qwDefinition := base.toCCM25TheoremBase.qwDefinition
  finitePrimeNormalization := common.finite_prime_normalization

def toCCM25TheoremBaseWithConcreteFinitePrime
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    CCM25TheoremBase where
  weilSymbols := base.ccm25Model.toWeilFormSymbols
  qwDefinition := base.toCCM25TheoremBase.qwDefinition
  psiSign := base.toCCM25TheoremBase.psiSign
  qwLambdaFormula := base.toCCM25TheoremBase.qwLambdaFormula
  finitePrimeNormalization := common.finite_prime_normalization
  poleNormalization := base.toCCM25TheoremBase.poleNormalization
  noSpectralShortcutImport := ccm25_no_spectral_shortcut_import

theorem toCCM25WeilObjectPackage_rows_eq
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    (common.toCCM25WeilObjectPackage).concreteArithmeticRows =
      common.concreteArithmeticRows :=
  rfl

theorem toCCM25WeilObjectPackage_symbols_eq
    {base : SourceObjectTheoremBasePackage}
    (common : SourceObjectCommonData base) :
    (common.toCCM25WeilObjectPackage).weilSymbols =
      base.ccm25Model.toWeilFormSymbols :=
  rfl

end SourceObjectCommonData

/--
Expanded row data after Goal 2C.

The CCM25 row is intentionally not a free field: it is computed from
`SourceObjectCommonData`, which already ties the arithmetic rows to the common
source test and the Goal 0E finite-prime theorem path.
-/
structure SourceObjectExpandedRows
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base) where
  ccm24 : SourceObject.CCM24SemilocalObjectPackage
  cc20Trace : SourceObject.CC20TraceObjectPackage
  cc20SupportSquareComparison :
    CC20Concrete.TraceScale.CC20TracePackageSupportSquareComparison cc20Trace

namespace SourceObjectExpandedRows

open CC20Concrete.TraceScale

abbrev CC20SupportSquareComparison :=
  CC20Concrete.TraceScale.CC20TracePackageSupportSquareComparison

abbrev CC20ScalarSupportSquareComparison :=
  CC20Concrete.TraceScale.CC20TracePackageScalarSupportSquareComparison

def normalizedCC20SupportSquareComparison
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed) :
    CC20SupportSquareComparison
      (CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        normalizedSeed remainders) :=
  CC20TracePackageSupportSquareComparison.forNormalizedSeedTraceObjectPackage
    normalizedSeed remainders

noncomputable def normalizedScalarCC20SupportSquareComparison
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed)) :
    CC20SupportSquareComparison
      (CC20Concrete.TraceScale.normalizedScalarTraceObjectPackage
        scalarSeed remainders) where
  normalizedSeed :=
    CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed scalarSeed
  remainders := remainders
  supportSquareTrace_eq := by
    apply heq_of_eq
    funext g
    exact
      CC20Concrete.TraceScale.normalized_scalar_as_legal_square_seed_support_square_eq_scalar
        scalarSeed g

noncomputable def normalizedScalarCC20ScalarSupportSquareComparison
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed)) :
    CC20ScalarSupportSquareComparison
      (CC20Concrete.TraceScale.normalizedScalarTraceObjectPackage
        scalarSeed remainders) :=
  open CC20Concrete.TraceScale.CC20TracePackageScalarSupportSquareComparison in
    forNormalizedScalarTraceObjectPackage scalarSeed remainders

def ofNormalizedCC20Trace
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed) :
    SourceObjectExpandedRows base common where
  ccm24 := ccm24
  cc20Trace :=
    CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
      normalizedSeed remainders
  cc20SupportSquareComparison :=
    normalizedCC20SupportSquareComparison normalizedSeed remainders

noncomputable def ofNormalizedScalarCC20Trace
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed)) :
    SourceObjectExpandedRows base common where
  ccm24 := ccm24
  cc20Trace :=
    CC20Concrete.TraceScale.normalizedScalarTraceObjectPackage
      scalarSeed remainders
  cc20SupportSquareComparison :=
    normalizedScalarCC20SupportSquareComparison scalarSeed remainders

theorem of_normalized_cc20_trace_cc20_trace_eq
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed) :
    (ofNormalizedCC20Trace (base := base) (common := common)
      ccm24 normalizedSeed remainders).cc20Trace =
      CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        normalizedSeed remainders :=
  rfl

theorem of_normalized_scalar_cc20_trace_cc20_trace_eq
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed)) :
    (ofNormalizedScalarCC20Trace (base := base) (common := common)
      ccm24 scalarSeed remainders).cc20Trace =
      CC20Concrete.TraceScale.normalizedScalarTraceObjectPackage
        scalarSeed remainders :=
  rfl

theorem of_normalized_cc20_trace_support_square_comparison
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed) :
    (ofNormalizedCC20Trace (base := base) (common := common)
      ccm24 normalizedSeed remainders).cc20SupportSquareComparison =
      normalizedCC20SupportSquareComparison normalizedSeed remainders :=
  rfl

theorem of_normalized_scalar_cc20_trace_support_square_comparison
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed)) :
    (ofNormalizedScalarCC20Trace (base := base) (common := common)
      ccm24 scalarSeed remainders).cc20SupportSquareComparison =
      normalizedScalarCC20SupportSquareComparison scalarSeed remainders :=
  rfl

def ccm25
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (_rows : SourceObjectExpandedRows base common) :
    SourceObject.CCM25WeilObjectPackage :=
  common.toCCM25WeilObjectPackage

theorem ccm25_rows_eq_common_rows
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (rows : SourceObjectExpandedRows base common) :
    rows.ccm25.concreteArithmeticRows = common.concreteArithmeticRows :=
  rfl

theorem ccm25_symbols_eq_base
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (rows : SourceObjectExpandedRows base common) :
    rows.ccm25.weilSymbols = base.ccm25Model.toWeilFormSymbols :=
  rfl

theorem ccm25_source_test_eq_arithmetic_rows
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (_rows : SourceObjectExpandedRows base common) :
    common.commonTest.ccm25SourceTest =
      CCM25Concrete.Rows.source_test_of_arithmetic_rows
        (ccm25 _rows).concreteArithmeticRows
        common.commonTest.sourceTest common.commonTest.sourceTest :=
  common.ccm25Test_eq_commonTest

theorem finite_prime_normalization
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (_rows : SourceObjectExpandedRows base common) :
    WeilFormSymbols.FinitePrimeNormalizationStatement
      (ccm25 _rows).weilSymbols :=
  common.finite_prime_normalization

def cc20_support_square_comparison
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (rows : SourceObjectExpandedRows base common) :
    CC20Concrete.TraceScale.CC20TracePackageSupportSquareComparison
      rows.cc20Trace :=
  rows.cc20SupportSquareComparison

theorem cc20_support_square_existing_identification
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (rows : SourceObjectExpandedRows base common) :
    HEq
      (ArchimedeanTraceSymbols.supportSquareTrace
        (CC20Concrete.TraceScale.normalizedSeedTraceObjectArchimedeanSymbols
          rows.cc20SupportSquareComparison.normalizedSeed
          rows.cc20SupportSquareComparison.remainders))
      rows.cc20Trace.archimedeanSymbols.supportSquareTrace :=
  rows.cc20SupportSquareComparison.supportSquareTrace_eq

def toPartialQWFinitePrime
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    (_rows : SourceObjectExpandedRows base common) :
    CCM25TheoremBasePartialQWFinitePrime :=
  common.toPartialQWFinitePrime

end SourceObjectExpandedRows

/--
Cross-object bridge data needed to assemble a `SourceObjectPackage`.

The bridge keeps the remaining mixed-row obligations explicit: common-test
involution, CCM24/CC20 common-test ownership, window controls, finite-prime
support matching, final sign compatibility, and the RH-exit bridge used by the
expanded CC20 exit object.
-/
structure SourceObjectCrossObjectBridges
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (rows : SourceObjectExpandedRows base common)
    (rhExit : SourceObject.CC20RHExitObjectPackage) where
  rhDefinitionBridge_eq_base :
    rhExit.rhDefinitionBridge = base.rhDefinitionBridge
  commonTestInvolution :
    SourceObject.CommonTestInvolutionBridge
      (SourceObjectExpandedRows.ccm25 rows).weilSymbols common.commonTest
  ccm24Test_eq_commonTest :
    SourceObject.CCM24CommonTestBridge
      (SourceObjectExpandedRows.ccm25 rows).weilSymbols
      common.commonTest rows.ccm24
  cc20TraceTest_eq_commonTest :
    SourceObject.CC20CommonTestBridge
      (SourceObjectExpandedRows.ccm25 rows).weilSymbols
      common.commonTest rows.cc20Trace
  convolutionSquare_eq_Fg : Prop
  ccm24Window_controls_qwLambda : Prop
  ccm24Window_controls_cdef : Prop
  finitePrimeSupport_matches_window : Prop
  qW_sign_bridge : Prop

namespace SourceObjectCrossObjectBridges

theorem ccm25_source_test_eq_arithmetic_rows
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (_bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    common.commonTest.ccm25SourceTest =
      CCM25Concrete.Rows.source_test_of_arithmetic_rows
        (SourceObjectExpandedRows.ccm25 rows).concreteArithmeticRows
        common.commonTest.sourceTest common.commonTest.sourceTest :=
  SourceObjectExpandedRows.ccm25_source_test_eq_arithmetic_rows rows

theorem rh_definition_bridge_eq_base
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    rhExit.rhDefinitionBridge = base.rhDefinitionBridge :=
  bridges.rhDefinitionBridge_eq_base

end SourceObjectCrossObjectBridges

/--
Goal 2D constructor for the expanded source-object package.

Every field is supplied by the staged base package, common-test data, expanded
rows, explicit RH-exit object, or named cross-object bridge data.  This is not
a no-argument source package and does not prove the remaining analytic rows.
-/
def sourceObjectPackageOfData
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (rows : SourceObjectExpandedRows base common)
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    SourceObject.SourceObjectPackage where
  ccm24 := rows.ccm24
  ccm25 := SourceObjectExpandedRows.ccm25 rows
  commonFinitePrimeArithmeticSourceDataOwner :=
    common.commonFinitePrimeArithmeticSourceDataOwner
  commonTest := common.commonTest
  cc20Trace := rows.cc20Trace
  cc20RHExit := rhExit
  commonTestInvolution := bridges.commonTestInvolution
  ccm24Test_eq_commonTest := bridges.ccm24Test_eq_commonTest
  ccm25Test_eq_commonTest :=
    SourceObjectExpandedRows.ccm25_source_test_eq_arithmetic_rows rows
  cc20TraceTest_eq_commonTest := bridges.cc20TraceTest_eq_commonTest
  convolutionSquare_eq_Fg := bridges.convolutionSquare_eq_Fg
  ccm24Window_controls_qwLambda := bridges.ccm24Window_controls_qwLambda
  ccm24Window_controls_cdef := bridges.ccm24Window_controls_cdef
  finitePrimeSupport_matches_window := bridges.finitePrimeSupport_matches_window
  qW_sign_bridge := bridges.qW_sign_bridge

def sourceObjectPackageOfNormalizedCC20Trace
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed)
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit) :
    SourceObject.SourceObjectPackage :=
  sourceObjectPackageOfData base common
    (SourceObjectExpandedRows.ofNormalizedCC20Trace
      ccm24 normalizedSeed remainders)
    rhExit bridges

noncomputable def sourceObjectPackageOfNormalizedScalarCC20Trace
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed))
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24 scalarSeed remainders)
        rhExit) :
    SourceObject.SourceObjectPackage :=
  sourceObjectPackageOfData base common
    (SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
      ccm24 scalarSeed remainders)
    rhExit bridges

/--
Source-object input for the normalized CC20 trace package.

This is the boundary where the compact theorem-base package becomes a full
source-object package: the CCM24 object, RH-exit object, and cross-object
bridges must be supplied together for the same normalized seed and remainder
data.
-/
structure NormalizedCC20SourceObjectLayerInput
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed) where
  ccm24 : SourceObject.CCM24SemilocalObjectPackage
  rhExit : SourceObject.CC20RHExitObjectPackage
  bridges :
    SourceObjectCrossObjectBridges base common
      (SourceObjectExpandedRows.ofNormalizedCC20Trace
        ccm24 normalizedSeed remainders)
      rhExit

namespace NormalizedCC20SourceObjectLayerInput

def rows
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols}
    {remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed}
    (input :
      NormalizedCC20SourceObjectLayerInput
        base common normalizedSeed remainders) :
    SourceObjectExpandedRows base common :=
  SourceObjectExpandedRows.ofNormalizedCC20Trace
    input.ccm24 normalizedSeed remainders

def package
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols}
    {remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        normalizedSeed}
    (input :
      NormalizedCC20SourceObjectLayerInput
        base common normalizedSeed remainders) :
    SourceObject.SourceObjectPackage :=
  sourceObjectPackageOfNormalizedCC20Trace
    base common input.ccm24 normalizedSeed remainders input.rhExit
    input.bridges

end NormalizedCC20SourceObjectLayerInput

/--
Source-object input for the scalar normalized CC20 trace package.

The scalar package reuses the same base/common/CCM24 objects but has its own
scalar CC20 trace object, RH-exit object, and bridge package.
-/
structure NormalizedScalarSourceObjectLayerInput
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed)) where
  rhExit : SourceObject.CC20RHExitObjectPackage
  bridges :
    SourceObjectCrossObjectBridges base common
      (SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
        ccm24 scalarSeed remainders)
      rhExit

namespace NormalizedScalarSourceObjectLayerInput

noncomputable def rows
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {ccm24 : SourceObject.CCM24SemilocalObjectPackage}
    {scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols}
    {remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed)}
    (_input :
      NormalizedScalarSourceObjectLayerInput
        base common ccm24 scalarSeed remainders) :
    SourceObjectExpandedRows base common :=
  SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
    ccm24 scalarSeed remainders

noncomputable def package
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {ccm24 : SourceObject.CCM24SemilocalObjectPackage}
    {scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols}
    {remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed)}
    (input :
      NormalizedScalarSourceObjectLayerInput
        base common ccm24 scalarSeed remainders) :
    SourceObject.SourceObjectPackage :=
  sourceObjectPackageOfNormalizedScalarCC20Trace
    base common ccm24 scalarSeed remainders input.rhExit input.bridges

end NormalizedScalarSourceObjectLayerInput

namespace SourceObjectPackageOfData

theorem normalized_cc20_trace_package_eq_data_constructor
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed)
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit) :
    sourceObjectPackageOfNormalizedCC20Trace
      base common ccm24 normalizedSeed remainders rhExit bridges =
      sourceObjectPackageOfData base common
        (SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit bridges :=
  rfl

theorem normalized_cc20_trace_package_cc20_trace_eq
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed)
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit) :
    (sourceObjectPackageOfNormalizedCC20Trace
      base common ccm24 normalizedSeed remainders rhExit bridges).cc20Trace =
      CC20Concrete.TraceScale.normalizedSeedTraceObjectPackage
        normalizedSeed remainders :=
  rfl

theorem normalized_scalar_cc20_trace_package_cc20_trace_eq
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed))
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24 scalarSeed remainders)
        rhExit) :
    (sourceObjectPackageOfNormalizedScalarCC20Trace
      base common ccm24 scalarSeed remainders rhExit bridges).cc20Trace =
      CC20Concrete.TraceScale.normalizedScalarTraceObjectPackage
        scalarSeed remainders :=
  rfl

def normalized_seed_ordinary_trace_support_square_statement
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols) :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        normalizedSeed).archimedeanSymbols :=
  normalizedSeed.ordinary_trace_support_square_statement

def normalized_seed_support_square_no_defect_statement
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols) :
    ∀ g :
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        normalizedSeed).archimedeanSymbols.Test,
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        normalizedSeed).archimedeanSymbols.traceClass g →
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        normalizedSeed).archimedeanSymbols.cyclicLegal g →
      (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        normalizedSeed).archimedeanSymbols.supportSquareTrace g =
        (CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
          normalizedSeed).archimedeanSymbols.sourceNoDefectTrace g :=
  CC20Concrete.TraceScale.ConcreteTraceScaleSymbols.support_square_no_defect_statement
    (CC20Concrete.TraceScale.normalizedSeedConcreteSymbols normalizedSeed)

theorem normalized_cc20_trace_package_ordinary_trace_support_square
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed)
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit) :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      (SourceObject.SourceObjectPackage.toArchimedeanTraceSymbols
        (sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)) :=
  normalized_seed_ordinary_trace_support_square_statement normalizedSeed

theorem normalized_cc20_trace_package_support_square_no_defect
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed)
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit) :
    let A :=
      SourceObject.SourceObjectPackage.toArchimedeanTraceSymbols
        (sourceObjectPackageOfNormalizedCC20Trace
          base common ccm24 normalizedSeed remainders rhExit bridges)
    ∀ g : A.Test, A.traceClass g → A.cyclicLegal g →
      A.supportSquareTrace g = A.sourceNoDefectTrace g :=
  normalized_seed_support_square_no_defect_statement normalizedSeed

theorem normalized_scalar_cc20_trace_package_source_no_defect_eq_scalar
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed))
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24 scalarSeed remainders)
        rhExit)
    (g : scalarSeed.Test) :
    let pkg :=
      sourceObjectPackageOfNormalizedScalarCC20Trace
        base common ccm24 scalarSeed remainders rhExit bridges
    pkg.cc20Trace.archimedeanSymbols.sourceNoDefectTrace g =
      scalarSeed.scalarTrace g := by
  intro pkg
  rfl

theorem normalized_scalar_cc20_trace_package_support_square_eq_scalar
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed))
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24 scalarSeed remainders)
        rhExit)
    (g : scalarSeed.Test) :
    let pkg :=
      sourceObjectPackageOfNormalizedScalarCC20Trace
        base common ccm24 scalarSeed remainders rhExit bridges
    pkg.cc20Trace.archimedeanSymbols.supportSquareTrace g =
      scalarSeed.scalarTrace g := by
  intro pkg
  rfl

theorem normalized_scalar_cc20_trace_package_support_square_no_defect
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed))
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24 scalarSeed remainders)
        rhExit) :
    let A :=
      SourceObject.SourceObjectPackage.toArchimedeanTraceSymbols
        (sourceObjectPackageOfNormalizedScalarCC20Trace
          base common ccm24 scalarSeed remainders rhExit bridges)
    ∀ g : A.Test, A.traceClass g → A.cyclicLegal g →
      A.supportSquareTrace g = A.sourceNoDefectTrace g := by
  intro A g _htrace _hcyclic
  rfl

def normalized_cc20_trace_package_support_square_comparison
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (normalizedSeed :
      CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData normalizedSeed)
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedCC20Trace
          ccm24 normalizedSeed remainders)
        rhExit) :
    CC20Concrete.TraceScale.CC20TracePackageSupportSquareComparison
      (sourceObjectPackageOfNormalizedCC20Trace
        base common ccm24 normalizedSeed remainders rhExit bridges).cc20Trace :=
  SourceObjectExpandedRows.cc20SupportSquareComparison
    (SourceObjectExpandedRows.ofNormalizedCC20Trace
      (base := base) (common := common) ccm24 normalizedSeed remainders)

noncomputable def normalized_scalar_cc20_trace_package_support_square_comparison
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed))
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24 scalarSeed remainders)
        rhExit) :
    CC20Concrete.TraceScale.CC20TracePackageSupportSquareComparison
      (sourceObjectPackageOfNormalizedScalarCC20Trace
        base common ccm24 scalarSeed remainders rhExit bridges).cc20Trace :=
  SourceObjectExpandedRows.cc20SupportSquareComparison
    (SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
      (base := base) (common := common) ccm24 scalarSeed remainders)

noncomputable def normalized_scalar_cc20_trace_package_scalar_support_square_comparison
    (base : SourceObjectTheoremBasePackage)
    (common : SourceObjectCommonData base)
    (ccm24 : SourceObject.CCM24SemilocalObjectPackage)
    (scalarSeed :
      CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols)
    (remainders :
      CC20Concrete.TraceScale.CC20TracePackageRemainderData
        (CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          scalarSeed))
    (rhExit : SourceObject.CC20RHExitObjectPackage)
    (_bridges :
      SourceObjectCrossObjectBridges base common
        (SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
          ccm24 scalarSeed remainders)
        rhExit) :
    CC20Concrete.TraceScale.CC20TracePackageScalarSupportSquareComparison
      (sourceObjectPackageOfNormalizedScalarCC20Trace
        base common ccm24 scalarSeed remainders rhExit _bridges).cc20Trace :=
  SourceObjectExpandedRows.normalizedScalarCC20ScalarSupportSquareComparison
    scalarSeed remainders

theorem ccm25_eq_rows
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    (sourceObjectPackageOfData base common rows rhExit bridges).ccm25 =
      SourceObjectExpandedRows.ccm25 rows :=
  rfl

theorem commonTest_eq_common
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    (sourceObjectPackageOfData base common rows rhExit bridges).commonTest =
      common.commonTest :=
  rfl

theorem ccm25_source_test_eq_arithmetic_rows
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    (sourceObjectPackageOfData base common rows rhExit bridges).ccm25Test_eq_commonTest =
      SourceObjectExpandedRows.ccm25_source_test_eq_arithmetic_rows rows :=
  rfl

theorem finite_prime_normalization
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    WeilFormSymbols.FinitePrimeNormalizationStatement
      (sourceObjectPackageOfData base common rows rhExit bridges).ccm25.weilSymbols :=
  SourceObjectExpandedRows.finite_prime_normalization rows

def cc20_support_square_comparison
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    CC20Concrete.TraceScale.CC20TracePackageSupportSquareComparison
      (sourceObjectPackageOfData base common rows rhExit bridges).cc20Trace :=
  rows.cc20SupportSquareComparison

theorem cc20_support_square_existing_identification
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    HEq
      (ArchimedeanTraceSymbols.supportSquareTrace
        (CC20Concrete.TraceScale.normalizedSeedTraceObjectArchimedeanSymbols
          rows.cc20SupportSquareComparison.normalizedSeed
          rows.cc20SupportSquareComparison.remainders))
      (ArchimedeanTraceSymbols.supportSquareTrace
        (SourceObject.CC20TraceObjectPackage.archimedeanSymbols
          (SourceObject.SourceObjectPackage.cc20Trace
            (sourceObjectPackageOfData base common rows rhExit bridges)))) :=
  SourceObjectExpandedRows.cc20_support_square_existing_identification rows

theorem rh_definition_bridge_eq_base
    {base : SourceObjectTheoremBasePackage}
    {common : SourceObjectCommonData base}
    {rows : SourceObjectExpandedRows base common}
    {rhExit : SourceObject.CC20RHExitObjectPackage}
    (bridges : SourceObjectCrossObjectBridges base common rows rhExit) :
    (sourceObjectPackageOfData base common rows rhExit bridges).cc20RHExit.rhDefinitionBridge =
      base.rhDefinitionBridge :=
  bridges.rhDefinitionBridge_eq_base

end SourceObjectPackageOfData

end Source
end ConnesWeilRH
