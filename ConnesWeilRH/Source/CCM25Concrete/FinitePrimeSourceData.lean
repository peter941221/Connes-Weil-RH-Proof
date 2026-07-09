/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeInterface
import ConnesWeilRH.Source.CCM25Concrete.CommonSourceTest
import ConnesWeilRH.Source.CCM25Concrete.Rows

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

noncomputable def SourceScopedRestrictedArchimedeanFormula
    (W : WeilFormSymbols) (f : TestFunction) (lambda : ℝ)
    (restrictedData :
      PrimePowerArithmetic.SourceRestrictedFinitePrimeArithmeticData
        W f f lambda) : ℝ :=
  W.archimedeanTerm (W.convolutionStar f f) +
      W.polePairing f -
        PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
          W f f lambda restrictedData

noncomputable def SourceScopedGlobalArchimedeanFormula
    (W : WeilFormSymbols) (f : TestFunction)
    (globalData :
      PrimePowerArithmetic.SourceGlobalFinitePrimeArithmeticData W f f) :
    ℝ :=
  W.poleFunctional (W.convolutionStar f f) -
    W.archimedeanTerm (W.convolutionStar f f) -
      PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
        W f f globalData

def SourceScopedArchimedeanContributionBalance
    (W : WeilFormSymbols) (f : TestFunction) (lambda : ℝ)
    (globalData :
      PrimePowerArithmetic.SourceGlobalFinitePrimeArithmeticData W f f)
    (restrictedData :
      PrimePowerArithmetic.SourceRestrictedFinitePrimeArithmeticData
        W f f lambda) : Prop :=
  SourceScopedRestrictedArchimedeanFormula W f lambda restrictedData =
    SourceScopedGlobalArchimedeanFormula W f globalData

structure SourceArchimedeanTermData
    (W : WeilFormSymbols) (f : TestFunction) where
  sourceConvolutionSquare : TestFunction
  sourceConvolutionSquareReadOff :
    sourceConvolutionSquare = W.convolutionStar f f
  sourceArchimedeanTerm : ℝ
  archimedeanTermReadOff :
    W.archimedeanTerm sourceConvolutionSquare = sourceArchimedeanTerm

namespace SourceArchimedeanTermData

def ofWeilFormSymbols
    (W : WeilFormSymbols) (f : TestFunction) :
    SourceArchimedeanTermData W f where
  sourceConvolutionSquare := W.convolutionStar f f
  sourceConvolutionSquareReadOff := rfl
  sourceArchimedeanTerm := W.archimedeanTerm (W.convolutionStar f f)
  archimedeanTermReadOff := rfl

theorem archimedeanTerm_convolutionStar
    {W : WeilFormSymbols} {f : TestFunction}
    (h : SourceArchimedeanTermData W f) :
    W.archimedeanTerm (W.convolutionStar f f) =
      h.sourceArchimedeanTerm := by
  rw [← h.sourceConvolutionSquareReadOff]
  exact h.archimedeanTermReadOff

end SourceArchimedeanTermData

structure FixedLambdaCommonFinitePrimeSupportData
    (W : WeilFormSymbols)
    (common : CommonSourceTest.ConcreteCommonSourceTest W)
    (lambda : ℝ) where
  globalIndexData :
    ∀ n : ℕ,
      n ∈ W.globalPrimeIndexSet →
        PrimePowerSupport.SourceGlobalIndexData
          W common.sourceTest common.sourceTest n
  routeVisibleGlobalIndex :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n
          (W.convolutionStar common.sourceTest common.sourceTest) →
        n ∈ W.globalPrimeIndexSet
  restrictedIndexData :
    ∀ n : ℕ,
      n ∈ W.restrictedPrimeIndexSet lambda →
        PrimePowerSupport.SourceRestrictedIndexData
          W common.sourceTest common.sourceTest lambda n
  routeVisibleRestrictedIndex :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n
          (W.convolutionStar common.sourceTest common.sourceTest) →
        1 < n → (n : ℝ) ≤ lambda ^ 2 →
        n ∈ W.restrictedPrimeIndexSet lambda

namespace FixedLambdaCommonFinitePrimeSupportData

theorem globalExact
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W}
    {lambda : ℝ}
    (data : FixedLambdaCommonFinitePrimeSupportData W common lambda)
    (n : ℕ) :
    n ∈ W.globalPrimeIndexSet ↔
      PrimePowerSupport.SourceGlobalIndexData
        W common.sourceTest common.sourceTest n := by
  constructor
  · exact data.globalIndexData n
  · intro hdata
    exact data.routeVisibleGlobalIndex n
      hdata.atomVisible

theorem restrictedExact
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W}
    {lambda : ℝ}
    (data : FixedLambdaCommonFinitePrimeSupportData W common lambda)
    (n : ℕ) :
    n ∈ W.restrictedPrimeIndexSet lambda ↔
      PrimePowerSupport.SourceRestrictedIndexData
        W common.sourceTest common.sourceTest lambda n := by
  constructor
  · exact data.restrictedIndexData n
  · intro hdata
    exact data.routeVisibleRestrictedIndex n
      hdata.atomVisible
      hdata.lambdaCut.1 hdata.lambdaCut.2

def ofConcreteCommonSupport
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W}
    {lambda : ℝ}
    (support :
      PrimePowerSupport.ConcreteCommonFixedLambdaPrimePowerSupport
        W common lambda) :
    FixedLambdaCommonFinitePrimeSupportData W common lambda where
  globalIndexData := by
    intro n hn
    let hdata := support.support.globalIndexData n hn
    exact
      { primePowerIndex := hdata.primePowerIndex
        atomVisible := hdata.atomVisible }
  routeVisibleGlobalIndex := support.support.routeVisibleGlobalIndex
  restrictedIndexData := by
    intro n hn
    let hdata := support.support.restrictedIndexData n hn
    exact
      { primePowerIndex := hdata.primePowerIndex
        atomVisible := hdata.atomVisible
        lambdaCut := hdata.lambdaCut }
  routeVisibleRestrictedIndex := support.support.routeVisibleRestrictedIndex

end FixedLambdaCommonFinitePrimeSupportData

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
  globalIndexData :
    ∀ n : ℕ,
      n ∈ W.globalPrimeIndexSet →
        PrimePowerSupport.SourceGlobalIndexData W f g n
  routeVisibleGlobalIndex :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) →
        n ∈ W.globalPrimeIndexSet
  restrictedIndexData :
    ∀ n : ℕ,
      n ∈ W.restrictedPrimeIndexSet lambda →
        PrimePowerSupport.SourceRestrictedIndexData W f g lambda n
  routeVisibleRestrictedIndex :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) →
        1 < n → (n : ℝ) ≤ lambda ^ 2 →
        n ∈ W.restrictedPrimeIndexSet lambda
  visibleArithmeticData :
    PrimePowerArithmetic.SourceVisibleFinitePrimeArithmeticData
      W f g sourceTest
  atoms :
    PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalizationForSourceTest
      W f g sourceTest

namespace FixedLambdaArithmeticCertificateSourceTestData

def sourceVisibleArithmeticData
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    {sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g}
    (data :
      FixedLambdaArithmeticCertificateSourceTestData
        W f g lambda sourceTest)
    (n : ℕ)
    (hn : sourceTest.sourceAtomVisible n) :
    PrimePowerArithmetic.SourceFinitePrimeArithmeticData W f g n :=
  data.visibleArithmeticData.atVisibleIndex n hn

/-- The certificate atom normalization agrees with the visible arithmetic data
on every source-visible atom.  This is not supplied by the basic certificate
record: `atoms` and `visibleArithmeticData` are independent fields unless a
stronger constructor or row supplies this read-off. -/
def DirectAtomVisibleReadOff
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    {sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g}
    (data :
      FixedLambdaArithmeticCertificateSourceTestData
        W f g lambda sourceTest) :
    Prop :=
  ∀ (n : ℕ) (hn : sourceTest.sourceAtomVisible n),
    (data.atoms.atIndex n).data =
      data.visibleArithmeticData.atVisibleIndex n hn

/-- Function-level form of `DirectAtomVisibleReadOff`.  This is the sharper
same-certificate API boundary: the visible slice of the atom normalization is
the visible arithmetic function. -/
def DirectAtomVisibleFunctionReadOff
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    {sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g}
    (data :
      FixedLambdaArithmeticCertificateSourceTestData
        W f g lambda sourceTest) :
    Prop :=
  (fun n hn => (data.atoms.atIndex n).data) =
    (fun n hn => data.visibleArithmeticData.atVisibleIndex n hn)

theorem DirectAtomVisibleReadOff_of_functionReadOff
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    {sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g}
    {data :
      FixedLambdaArithmeticCertificateSourceTestData
        W f g lambda sourceTest}
    (h :
      DirectAtomVisibleFunctionReadOff data) :
    DirectAtomVisibleReadOff data := by
  intro n hn
  exact congrFun (congrFun h n) hn

theorem globalExact
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    {sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g}
    (data :
      FixedLambdaArithmeticCertificateSourceTestData
        W f g lambda sourceTest)
    (n : ℕ) :
    n ∈ W.globalPrimeIndexSet ↔
      PrimePowerSupport.SourceGlobalIndexData W f g n := by
  constructor
  · exact data.globalIndexData n
  · intro hdata
    exact data.routeVisibleGlobalIndex n
      hdata.atomVisible

theorem restrictedExact
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    {sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g}
    (data :
      FixedLambdaArithmeticCertificateSourceTestData
        W f g lambda sourceTest)
    (n : ℕ) :
    n ∈ W.restrictedPrimeIndexSet lambda ↔
      PrimePowerSupport.SourceRestrictedIndexData W f g lambda n := by
  constructor
  · exact data.restrictedIndexData n
  · intro hdata
    exact data.routeVisibleRestrictedIndex n
      hdata.atomVisible
      hdata.lambdaCut.1 hdata.lambdaCut.2

theorem visibleIff
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    {sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g}
    (data :
      FixedLambdaArithmeticCertificateSourceTestData
        W f g lambda sourceTest)
    (n : ℕ) :
    W.finitePrimeAtomVisible n (W.convolutionStar f g) ↔
      PrimePowerSupport.SourceVisibleAtomData W f g n := by
  constructor
  · intro hvisible
    have hsourceVisible :
        sourceTest.sourceAtomVisible n :=
      (PrimePowerTest.route_visibility_iff_source_visibility sourceTest n).1
        hvisible
    exact
      { primePowerIndex :=
          (data.sourceVisibleArithmeticData n hsourceVisible).sourcePrimePowerIndex
        atomVisible := hvisible }
  · intro hdata
    exact hdata.atomVisible

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
  visibleArithmeticData := data.visibleArithmeticData
  globalIndexData := by
    intro n hn
    let hdata := data.globalIndexData n hn
    exact
      { primePowerIndex := hdata.primePowerIndex
        atomVisible := hdata.atomVisible }
  routeVisibleGlobalIndex := data.routeVisibleGlobalIndex
  restrictedIndexData := by
    intro n hn
    let hdata := data.restrictedIndexData n hn
    exact
      { primePowerIndex := hdata.primePowerIndex
        atomVisible := hdata.atomVisible
        lambdaCut := hdata.lambdaCut }
  routeVisibleRestrictedIndex := data.routeVisibleRestrictedIndex

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
  atomsWithSourceTest := data.atoms

/--
Lower constructor from the arithmetic support skeleton.

This keeps the exact finite-prime support/cutoff rows sourced from
`PrimePowerSupport.SourcePrimePowerArithmeticSupportSkeletonAtLambda`; the
source-test data record becomes a consumer of that lower support object.
-/
def ofArithmeticSupportSkeleton
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (support :
      PrimePowerSupport.SourcePrimePowerArithmeticSupportSkeletonAtLambda
        W f g lambda)
    (atoms :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalizationForSourceTest
        W f g support.sourceTest) :
    FixedLambdaArithmeticCertificateSourceTestData
      W f g lambda support.sourceTest where
  globalIndexData := by
    intro n hn
    let hdata := support.globalIndexData n hn
    exact
      { primePowerIndex := hdata.primePowerIndex
        atomVisible := hdata.atomVisible }
  routeVisibleGlobalIndex := support.routeVisibleGlobalIndex
  restrictedIndexData := by
    intro n hn
    let hdata := support.restrictedIndexData n hn
    exact
      { primePowerIndex := hdata.primePowerIndex
        atomVisible := hdata.atomVisible
        lambdaCut := hdata.lambdaCut }
  routeVisibleRestrictedIndex := support.routeVisibleRestrictedIndex
  visibleArithmeticData := support.visibleArithmeticData
  atoms := atoms

@[simp] theorem ofArithmeticSupportSkeleton_visibleArithmeticData
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (support :
      PrimePowerSupport.SourcePrimePowerArithmeticSupportSkeletonAtLambda
        W f g lambda)
    (atoms :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalizationForSourceTest
        W f g support.sourceTest) :
    (ofArithmeticSupportSkeleton support atoms).visibleArithmeticData =
      support.visibleArithmeticData :=
  rfl

@[simp] theorem ofArithmeticSupportSkeleton_atoms
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (support :
      PrimePowerSupport.SourcePrimePowerArithmeticSupportSkeletonAtLambda
        W f g lambda)
    (atoms :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalizationForSourceTest
        W f g support.sourceTest) :
    (ofArithmeticSupportSkeleton support atoms).atoms = atoms :=
  rfl

noncomputable def ofConcreteObject
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (object :
      FinitePrimeCertificate.FixedLambdaFinitePrimeConcreteObject
        W f g lambda) :
    FixedLambdaArithmeticCertificateSourceTestData
      W f g lambda object.sourceTest where
  globalIndexData := by
    intro n hn
    let hdata := object.certificate.support.globalIndexData n hn
    exact
      { primePowerIndex := hdata.primePowerIndex
        atomVisible := hdata.atomVisible }
  routeVisibleGlobalIndex :=
    object.certificate.support.routeVisibleGlobalIndex
  restrictedIndexData := by
    intro n hn
    let hdata := object.certificate.support.restrictedIndexData n hn
    exact
      { primePowerIndex := hdata.primePowerIndex
        atomVisible := hdata.atomVisible
        lambdaCut := hdata.lambdaCut }
  routeVisibleRestrictedIndex :=
    object.certificate.support.routeVisibleRestrictedIndex
  visibleArithmeticData := object.visibleArithmeticData
  atoms := object.certificate.atomsWithSourceTest

@[simp] theorem ofConcreteObject_visibleArithmeticData
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (object :
      FinitePrimeCertificate.FixedLambdaFinitePrimeConcreteObject
        W f g lambda) :
    (ofConcreteObject object).visibleArithmeticData =
      object.visibleArithmeticData :=
  rfl

@[simp] theorem ofConcreteObject_atoms
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (object :
      FinitePrimeCertificate.FixedLambdaFinitePrimeConcreteObject
        W f g lambda) :
    (ofConcreteObject object).atoms = object.certificate.atomsWithSourceTest :=
  rfl

theorem directAtomVisibleFunctionReadOff_ofConcreteObject
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (object :
      FinitePrimeCertificate.FixedLambdaFinitePrimeConcreteObject
        W f g lambda) :
    DirectAtomVisibleFunctionReadOff (ofConcreteObject object) := by
  funext n hn
  rfl

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
      W f g lambda cert.support.sourceTest :=
  FixedLambdaArithmeticCertificateSourceTestData.ofArithmeticSupportSkeleton
    cert.support
    cert.atomsWithSourceTest

@[simp] theorem fixedLambdaArithmeticCertificateSourceTestDataOfCertificate_visibleArithmeticData
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (cert :
      FinitePrimeCertificate.FixedLambdaFinitePrimeArithmeticCertificate
        W f g lambda) :
    (fixedLambdaArithmeticCertificateSourceTestDataOfCertificate
      cert).visibleArithmeticData =
      cert.support.visibleArithmeticData :=
  rfl

@[simp] theorem fixedLambdaArithmeticCertificateSourceTestDataOfCertificate_atoms
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (cert :
      FinitePrimeCertificate.FixedLambdaFinitePrimeArithmeticCertificate
        W f g lambda) :
    (fixedLambdaArithmeticCertificateSourceTestDataOfCertificate cert).atoms =
      cert.atomsWithSourceTest :=
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

namespace FinitePrimeArithmeticSourceData

/-- Source-data-level version of direct atom/visible read-off.  It is the
route-independent bottom below route-specific source-test casts. -/
def CertificateDirectAtomVisibleReadOff
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W}
    (data : FinitePrimeArithmeticSourceData W common) :
    Prop :=
  ∀ (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda),
    FixedLambdaArithmeticCertificateSourceTestData.DirectAtomVisibleReadOff
      (data.certificateData f g lambda hlambda)

/-- Function-level source-data row below
`CertificateDirectAtomVisibleReadOff`. -/
def CertificateDirectAtomVisibleFunctionReadOff
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W}
    (data : FinitePrimeArithmeticSourceData W common) :
    Prop :=
  ∀ (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda),
    FixedLambdaArithmeticCertificateSourceTestData.DirectAtomVisibleFunctionReadOff
      (data.certificateData f g lambda hlambda)

/-- Constructor-provenance row below the atom/visible function read-off: each
fixed-lambda certificate is the source-data form of a concrete finite-prime
object.  Heterogeneous equality is used because the source-test index of the
concrete object may be definitionally presented differently from the selector
source-test stored in the source-data owner. -/
def CertificateConcreteObjectDataReadOff
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W}
    (data : FinitePrimeArithmeticSourceData W common) :
    Prop :=
  ∀ (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda),
    ∃ object :
        FinitePrimeCertificate.FixedLambdaFinitePrimeConcreteObject
          W f g lambda,
      HEq
        (FixedLambdaArithmeticCertificateSourceTestData.ofConcreteObject
          object)
        (data.certificateData f g lambda hlambda)

theorem CertificateDirectAtomVisibleReadOff_of_functionReadOff
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W}
    {data : FinitePrimeArithmeticSourceData W common}
    (h : CertificateDirectAtomVisibleFunctionReadOff data) :
    CertificateDirectAtomVisibleReadOff data := by
  intro f g lambda hlambda
  exact
    FixedLambdaArithmeticCertificateSourceTestData.DirectAtomVisibleReadOff_of_functionReadOff
      (h f g lambda hlambda)

end FinitePrimeArithmeticSourceData

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
      ∀ globalData :
        PrimePowerArithmetic.SourceGlobalFinitePrimeArithmeticData
          W commonTestFunction commonTestFunction,
      ∀ restrictedData :
        PrimePowerArithmetic.SourceRestrictedFinitePrimeArithmeticData
          W commonTestFunction commonTestFunction lambda,
        SourceScopedArchimedeanContributionBalance
          W commonTestFunction lambda globalData restrictedData

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
        ∀ globalData :
          PrimePowerArithmetic.SourceGlobalFinitePrimeArithmeticData
            W commonTestFunction commonTestFunction,
        ∀ restrictedData :
          PrimePowerArithmetic.SourceRestrictedFinitePrimeArithmeticData
            W commonTestFunction commonTestFunction lambda,
          SourceScopedArchimedeanContributionBalance
            W commonTestFunction lambda globalData restrictedData) :
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
        ∀ globalData :
          PrimePowerArithmetic.SourceGlobalFinitePrimeArithmeticData
            W commonTestFunction commonTestFunction,
        ∀ restrictedData :
          PrimePowerArithmetic.SourceRestrictedFinitePrimeArithmeticData
            W commonTestFunction commonTestFunction lambda,
          SourceScopedArchimedeanContributionBalance
            W commonTestFunction lambda globalData restrictedData) :
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
