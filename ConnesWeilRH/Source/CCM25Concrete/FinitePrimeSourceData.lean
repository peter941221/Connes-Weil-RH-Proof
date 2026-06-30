/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeInterface
import ConnesWeilRH.Source.CCM25Concrete.CommonSourceTest
import ConnesWeilRH.Source.CCM25Concrete.Rows
import ConnesWeilRH.Source.CCM25Concrete.Package

/-!
# CCM25 exact finite-prime source data

This module contains the source-facing exact finite-prime data required by the
normalized route.  It deliberately lives in the source layer rather than the
development skeleton, because the fixed-lambda arithmetic certificates are part
of the mathematical proof boundary.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace FinitePrimeSourceData

def ScopedArchimedeanContributionBalance
    (W : WeilFormSymbols) (f : TestFunction) (lambda : ℝ)
    (pkg : Package.ConcreteCCM25ArithmeticPackage W f lambda) : Prop :=
  W.archimedeanTerm (W.convolutionStar f f) +
      W.polePairing f -
        Package.source_restricted_finite_prime_evaluator_scoped_sum pkg =
    W.poleFunctional (W.convolutionStar f f) -
      W.archimedeanTerm (W.convolutionStar f f) -
        Package.source_global_finite_prime_evaluator_scoped_sum pkg

/-- Source-test selector for all CCM25 test pairs, anchored at one common test. -/
structure FinitePrimeSourceTestSelectorData
    (W : WeilFormSymbols)
    (common : CommonSourceTest.ConcreteCommonSourceTest W) where
  sourceTest :
    ∀ f g : TestFunction,
      PrimePowerTest.SourceTestEvaluationInterface W f g
  commonPairSourceTest :
    sourceTest common.sourceTest common.sourceTest =
      common.toSourceTestEvaluationInterface

/--
Fixed-lambda arithmetic certificate data with its source-test interface kept
visible.
-/
structure FixedLambdaArithmeticCertificateSourceTestData
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ)
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g) where
  visibleIff :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) ↔
        PrimePowerSupport.SourceVisibleAtomData
          PrimePowerArithmetic.SourcePrimePowerIndex
          sourceTest.sourceAtomVisible n
  globalExact :
    ∀ n : ℕ,
      n ∈ W.globalPrimeIndexSet ↔
        PrimePowerSupport.SourceGlobalIndexData
          PrimePowerArithmetic.SourcePrimePowerIndex
          sourceTest.sourceAtomVisible n
  restrictedExact :
    ∀ n : ℕ,
      n ∈ W.restrictedPrimeIndexSet lambda ↔
        PrimePowerSupport.SourceRestrictedIndexData
          PrimePowerArithmetic.SourcePrimePowerIndex
          sourceTest.sourceAtomVisible lambda n
  visibleAtomsInLambdaCut :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) →
        PrimePowerSupport.SourceLambdaCut lambda n
  atoms :
    PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalization W f g
  atomsUseSourceTest :
    PrimePowerArithmetic.UsesSourceTest atoms sourceTest

namespace FixedLambdaArithmeticCertificateSourceTestData

def toSupport
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    {sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g}
    (data :
      FixedLambdaArithmeticCertificateSourceTestData
        W f g lambda sourceTest)
    (hlambda : 1 < lambda) :
    PrimePowerSupport.SourcePrimePowerArithmeticSupportSkeletonAtLambda
      W f g lambda where
  oneLtLambda := hlambda
  sourceTest := sourceTest
  visibleIff := data.visibleIff
  globalExact := data.globalExact
  restrictedExact := data.restrictedExact
  visibleAtomsInLambdaCut := data.visibleAtomsInLambdaCut

def toCertificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    {sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g}
    (data :
      FixedLambdaArithmeticCertificateSourceTestData
        W f g lambda sourceTest)
    (hlambda : 1 < lambda) :
    FinitePrimeCertificate.FixedLambdaFinitePrimeArithmeticCertificate
      W f g lambda where
  support := data.toSupport hlambda
  atoms := data.atoms
  atomsUseSupportSourceTest := data.atomsUseSourceTest

theorem toCertificate_support_sourceTest
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    {sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g}
    (data :
      FixedLambdaArithmeticCertificateSourceTestData
        W f g lambda sourceTest)
    (hlambda : 1 < lambda) :
    (data.toCertificate hlambda).support.sourceTest = sourceTest :=
  rfl

end FixedLambdaArithmeticCertificateSourceTestData

def fixedLambdaArithmeticCertificateSourceTestDataOfCertificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (cert :
      FinitePrimeCertificate.FixedLambdaFinitePrimeArithmeticCertificate
        W f g lambda) :
    FixedLambdaArithmeticCertificateSourceTestData
      W f g lambda cert.support.sourceTest where
  visibleIff := cert.support.visibleIff
  globalExact := cert.support.globalExact
  restrictedExact := cert.support.restrictedExact
  visibleAtomsInLambdaCut := cert.support.visibleAtomsInLambdaCut
  atoms := cert.atoms
  atomsUseSourceTest := cert.atomsUseSupportSourceTest

theorem toCertificate_of_arithmetic_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (cert :
      FinitePrimeCertificate.FixedLambdaFinitePrimeArithmeticCertificate
        W f g lambda) :
    (fixedLambdaArithmeticCertificateSourceTestDataOfCertificate
        cert).toCertificate cert.support.oneLtLambda = cert :=
  rfl

/-- Exact finite-prime arithmetic data for all test pairs over one common test. -/
structure FinitePrimeArithmeticSourceData
    (W : WeilFormSymbols)
    (common : CommonSourceTest.ConcreteCommonSourceTest W) where
  selector : FinitePrimeSourceTestSelectorData W common
  certificateData :
    ∀ f g : TestFunction, ∀ lambda : ℝ,
      1 < lambda →
      FixedLambdaArithmeticCertificateSourceTestData
        W f g lambda (selector.sourceTest f g)

def finitePrimeArithmeticSourceDataOfSourceTestCertificates
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W)
    (certs :
      FinitePrimeInterface.FixedLambdaArithmeticSourceTestCertificatesForAllTests
        W)
    (commonPairSourceTest :
      (certs common.sourceTest common.sourceTest).sourceTest =
        common.toSourceTestEvaluationInterface) :
    FinitePrimeArithmeticSourceData W common where
  selector :=
    { sourceTest := fun f g => (certs f g).sourceTest
      commonPairSourceTest := commonPairSourceTest }
  certificateData := by
    intro f g lambda hlambda
    let cert := (certs f g).certificate lambda hlambda
    have hsource :
        cert.support.sourceTest = (certs f g).sourceTest :=
      (certs f g).certificateSourceTest lambda hlambda
    change
      FixedLambdaArithmeticCertificateSourceTestData
        W f g lambda (certs f g).sourceTest
    rw [← hsource]
    exact fixedLambdaArithmeticCertificateSourceTestDataOfCertificate cert

/-- Common-test finite-prime source data used by source-object packages. -/
structure CommonFinitePrimeArithmeticSourceData
    (W : WeilFormSymbols) where
  commonTestFunction : TestFunction
  finitePrimeData :
    FinitePrimeArithmeticSourceData W
      (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
  scopedArchimedeanContributionBalance :
    ∀ lambda : ℝ,
      ∀ pkg : Package.ConcreteCCM25ArithmeticPackage
        W commonTestFunction lambda,
        ScopedArchimedeanContributionBalance W commonTestFunction lambda pkg

def commonFinitePrimeArithmeticSourceDataOfSourceTestCertificates
    {W : WeilFormSymbols}
    (commonTestFunction : TestFunction)
    (certs :
      FinitePrimeInterface.FixedLambdaArithmeticSourceTestCertificatesForAllTests
        W)
    (commonPairSourceTest :
      (certs commonTestFunction commonTestFunction).sourceTest =
        (CommonSourceTest.concreteCommonSourceTest
          W commonTestFunction).toSourceTestEvaluationInterface)
    (scopedArchimedeanContributionBalance :
      ∀ lambda : ℝ,
        ∀ pkg : Package.ConcreteCCM25ArithmeticPackage
          W commonTestFunction lambda,
          ScopedArchimedeanContributionBalance
            W commonTestFunction lambda pkg) :
    CommonFinitePrimeArithmeticSourceData W where
  commonTestFunction := commonTestFunction
  finitePrimeData :=
    finitePrimeArithmeticSourceDataOfSourceTestCertificates
      (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
      certs commonPairSourceTest
  scopedArchimedeanContributionBalance :=
    scopedArchimedeanContributionBalance

def finitePrimeArithmeticSourceDataOfArithmeticRows
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W)
    (rows : Rows.ConcreteCCM25ArithmeticRows W)
    (commonPairSourceTest :
      Rows.source_test_of_arithmetic_rows
          rows common.sourceTest common.sourceTest =
        common.toSourceTestEvaluationInterface) :
    FinitePrimeArithmeticSourceData W common :=
  finitePrimeArithmeticSourceDataOfSourceTestCertificates
    common rows.finitePrimeArithmeticCertificates
    (by
      simpa [Rows.source_test_of_arithmetic_rows]
        using commonPairSourceTest)

def commonFinitePrimeArithmeticSourceDataOfArithmeticRows
    {W : WeilFormSymbols}
    (commonTestFunction : TestFunction)
    (rows : Rows.ConcreteCCM25ArithmeticRows W)
    (commonPairSourceTest :
      Rows.source_test_of_arithmetic_rows
          rows commonTestFunction commonTestFunction =
        (CommonSourceTest.concreteCommonSourceTest
          W commonTestFunction).toSourceTestEvaluationInterface)
    (scopedArchimedeanContributionBalance :
      ∀ lambda : ℝ,
        ∀ pkg : Package.ConcreteCCM25ArithmeticPackage
          W commonTestFunction lambda,
          ScopedArchimedeanContributionBalance
            W commonTestFunction lambda pkg) :
    CommonFinitePrimeArithmeticSourceData W where
  commonTestFunction := commonTestFunction
  finitePrimeData :=
    finitePrimeArithmeticSourceDataOfArithmeticRows
      (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
      rows commonPairSourceTest
  scopedArchimedeanContributionBalance :=
    scopedArchimedeanContributionBalance

def fixedLambdaArithmeticCertificatesForAllTests
    {W : WeilFormSymbols}
    (data : CommonFinitePrimeArithmeticSourceData W) :
    FinitePrimeInterface.FixedLambdaArithmeticCertificatesForAllTests W := by
  intro f g lambda hlambda
  exact
    (data.finitePrimeData.certificateData f g lambda hlambda).toCertificate
      hlambda

theorem fixedLambdaArithmeticCertificateSourceTest
    {W : WeilFormSymbols}
    (data : CommonFinitePrimeArithmeticSourceData W)
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    ((fixedLambdaArithmeticCertificatesForAllTests data
          f g lambda hlambda).support.sourceTest =
      data.finitePrimeData.selector.sourceTest f g) :=
  rfl

def fixedLambdaArithmeticSourceTestCertificatesForAllTests
    {W : WeilFormSymbols}
    (data : CommonFinitePrimeArithmeticSourceData W) :
    FinitePrimeInterface.FixedLambdaArithmeticSourceTestCertificatesForAllTests
      W := by
  intro f g
  exact
    { sourceTest := data.finitePrimeData.selector.sourceTest f g
      certificate := fixedLambdaArithmeticCertificatesForAllTests data f g
      certificateSourceTest :=
        fixedLambdaArithmeticCertificateSourceTest data f g }

theorem commonPairSourceTest
    {W : WeilFormSymbols}
    (data : CommonFinitePrimeArithmeticSourceData W) :
    data.finitePrimeData.selector.sourceTest data.commonTestFunction
        data.commonTestFunction =
      (CommonSourceTest.concreteCommonSourceTest
        W data.commonTestFunction).toSourceTestEvaluationInterface :=
  data.finitePrimeData.selector.commonPairSourceTest

end FinitePrimeSourceData
end CCM25Concrete
end Source
end ConnesWeilRH
