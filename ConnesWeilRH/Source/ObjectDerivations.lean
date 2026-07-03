/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.Objects

/-!
# Compact records derived from expanded source objects

The route still consumes the compact records from `ConnesWeilRH.Basic`. This
module proves that those compact records can be obtained as projections from
the expanded source-object package, rather than being treated as unrelated
route-local evidence.
-/

namespace ConnesWeilRH
namespace Source
namespace SourceObject

namespace SourceObjectPackage

def toSemilocalModelSymbols
    (pkg : SourceObjectPackage) : SemilocalModelSymbols :=
  pkg.ccm24.semilocalSymbols

def toWeilFormSymbols
    (pkg : SourceObjectPackage) : WeilFormSymbols :=
  pkg.ccm25.weilSymbols

def toCCM25CommonSourceTest
    (pkg : SourceObjectPackage) :
    CCM25Concrete.PrimePowerTest.SourceTestEvaluationInterface
      pkg.toWeilFormSymbols pkg.commonTest.sourceTest
      pkg.commonTest.sourceTest :=
  pkg.commonTest.ccm25SourceTest

theorem common_convolution_square_eq_ccm25_source_test_square
    (pkg : SourceObjectPackage) :
    pkg.commonTest.sourceConvolutionSquare =
      (toCCM25CommonSourceTest pkg).sourceConvolutionSquare := by
  exact pkg.commonTest.ccm25SourceTestSquareReadOff.symm

theorem common_ccm25_source_test_eq_arithmetic_rows
    (pkg : SourceObjectPackage) :
    toCCM25CommonSourceTest pkg =
      CCM25Concrete.Rows.source_test_of_arithmetic_rows
        pkg.ccm25.concreteArithmeticRows
        pkg.commonTest.sourceTest pkg.commonTest.sourceTest :=
  pkg.ccm25Test_eq_commonTest

def commonTestInvolutionBridge
    (pkg : SourceObjectPackage) :
    CommonTestInvolutionBridge pkg.toWeilFormSymbols pkg.commonTest :=
  pkg.commonTestInvolution

def ccm24CommonTestBridge
    (pkg : SourceObjectPackage) :
    CCM24CommonTestBridge pkg.toWeilFormSymbols pkg.commonTest pkg.ccm24 :=
  pkg.ccm24Test_eq_commonTest

def cc20CommonTestBridge
    (pkg : SourceObjectPackage) :
    CC20CommonTestBridge pkg.toWeilFormSymbols pkg.commonTest pkg.cc20Trace :=
  pkg.cc20TraceTest_eq_commonTest

theorem ccm24_common_support_window
    (pkg : SourceObjectPackage) :
    pkg.ccm24.semilocalSymbols.supportInWindow
      pkg.ccm24.sourceTestLeg pkg.ccm24.sourceSupportWindow :=
  pkg.ccm24.sourceSupportInWindowData

theorem ccm24_common_fourier_window
    (pkg : SourceObjectPackage) :
    pkg.ccm24.semilocalSymbols.fourierSupportInWindow
      pkg.ccm24.sourceTestLeg pkg.ccm24.sourceSupportWindow :=
  pkg.ccm24.sourceFourierSupportInWindowData

theorem ccm24_common_convolution_support_transported
    (pkg : SourceObjectPackage) :
    pkg.ccm24.semilocalSymbols.convolutionSupportTransported
      pkg.ccm24.sourceTestLeg pkg.ccm24.sourceSupportWindow :=
  (pkg.ccm24.sourceSupportAndFourierSupportTransport
    pkg.ccm24.sourceTestLeg
    pkg.ccm24.sourceSupportWindow
    pkg.ccm24.sourceSupportInWindowData
    pkg.ccm24.sourceFourierSupportInWindowData).2

theorem cc20_common_mellin_half_density
    (pkg : SourceObjectPackage) :
    ArchimedeanTraceSymbols.MellinHalfDensityConventionStatement
      pkg.cc20Trace.archimedeanSymbols :=
  (cc20CommonTestBridge pkg).halfDensityMatchesCommonTest

def toArchimedeanTraceSymbols
    (pkg : SourceObjectPackage) : ArchimedeanTraceSymbols :=
  pkg.cc20Trace.archimedeanSymbols

def toFiniteVanishingCriterionPackage
    (pkg : SourceObjectPackage) : FiniteVanishingCriterionPackage where
  finiteSetAdmissible :=
    SourceFiniteSetAdmissibility
      pkg.cc20RHExit.sourceFiniteVanishingCriterionPackage.finiteVanishingSet
  criterion :=
    (SourceFiniteVanishingCriterionPackage.toFiniteVanishingCriterionPackage
      pkg.cc20RHExit.sourceFiniteVanishingCriterionPackage).criterion

theorem provesCanonicalSemilocalModelStatement
    (pkg : SourceObjectPackage) :
    SemilocalModelSymbols.CanonicalSemilocalModelStatement
      pkg.toSemilocalModelSymbols :=
  pkg.ccm24.sourceCanonicalSemilocalModel

theorem provesSupportTransportStatement
    (pkg : SourceObjectPackage) :
    SemilocalModelSymbols.SupportTransportStatement
      pkg.toSemilocalModelSymbols :=
  pkg.ccm24.sourceSupportAndFourierSupportTransport

theorem provesBoundedComparisonStatement
    (pkg : SourceObjectPackage) :
    SemilocalModelSymbols.BoundedComparisonStatement
      pkg.toSemilocalModelSymbols :=
  pkg.ccm24.sourceBoundedComparisonTraceClassTransport

theorem provesSoninComparisonStatement
    (pkg : SourceObjectPackage) :
    SemilocalModelSymbols.SoninComparisonStatement
      pkg.toSemilocalModelSymbols :=
  pkg.ccm24.sourceFixedWindowSoninExhaustion

theorem provesQWDefinitionStatement
    (pkg : SourceObjectPackage) :
    WeilFormSymbols.QWDefinitionStatement pkg.toWeilFormSymbols :=
  CCM25Concrete.Rows.qw_definition_of_arithmetic_rows
    pkg.ccm25.concreteArithmeticRows

theorem provesPsiSignStatement
    (pkg : SourceObjectPackage) :
    WeilFormSymbols.PsiSignStatement pkg.toWeilFormSymbols :=
  CCM25Concrete.Rows.psi_sign_of_arithmetic_rows
    pkg.ccm25.concreteArithmeticRows

theorem provesQWLambdaFormulaStatement
    (pkg : SourceObjectPackage) :
    WeilFormSymbols.QWLambdaFormulaStatement pkg.toWeilFormSymbols :=
  CCM25Concrete.Rows.qw_lambda_formula_of_arithmetic_rows
    pkg.ccm25.concreteArithmeticRows

theorem provesFinitePrimeNormalizationStatement
    (pkg : SourceObjectPackage) :
    WeilFormSymbols.FinitePrimeNormalizationStatement
      pkg.toWeilFormSymbols :=
  CCM25Concrete.Rows.finite_prime_normalization_of_arithmetic_rows
    pkg.ccm25.concreteArithmeticRows

theorem provesFinitePrimePointwiseTermStatement
    (pkg : SourceObjectPackage) :
    ∀ f g : TestFunction,
      WeilFormSymbols.FinitePrimeTermNormalizationStatement
        pkg.toWeilFormSymbols f g :=
  fun f g =>
    CCM25Concrete.Rows.finite_prime_term_normalization_of_arithmetic_rows
      pkg.ccm25.concreteArithmeticRows f g

theorem provesPoleNormalizationStatement
    (pkg : SourceObjectPackage) :
    WeilFormSymbols.PoleNormalizationStatement pkg.toWeilFormSymbols :=
  CCM25Concrete.Rows.pole_normalization_of_arithmetic_rows
    pkg.ccm25.concreteArithmeticRows

theorem provesTraceSquareStatement
    (pkg : SourceObjectPackage) :
    ArchimedeanTraceSymbols.TraceSquareStatement
      pkg.toArchimedeanTraceSymbols := by
  intro g htrace hcyclic
  exact
    ⟨pkg.cc20Trace.sourceSupportSquareTraceReadOff g htrace hcyclic,
      pkg.cc20Trace.sourcePositiveTraceNonnegative g htrace hcyclic⟩

theorem provesOrdinaryTraceSupportSquareStatement
    (pkg : SourceObjectPackage) :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      pkg.toArchimedeanTraceSymbols :=
  pkg.cc20Trace.sourceOrdinaryTraceSupportSquare

theorem provesTraceClassTemplateStatement
    (pkg : SourceObjectPackage) :
    ArchimedeanTraceSymbols.TraceClassTemplateStatement
      pkg.toArchimedeanTraceSymbols :=
  pkg.cc20Trace.sourceTraceClassCyclicityTemplate

theorem provesMellinHalfDensityConventionStatement
    (pkg : SourceObjectPackage) :
    ArchimedeanTraceSymbols.MellinHalfDensityConventionStatement
      pkg.toArchimedeanTraceSymbols :=
  pkg.cc20Trace.sourceMellinHalfDensityCompatibility

theorem provesSignsAndNormalizationsStatement
    (pkg : SourceObjectPackage) :
    ArchimedeanTraceSymbols.SignsAndNormalizationsStatement
      pkg.toArchimedeanTraceSymbols :=
  pkg.cc20Trace.sourceCC20SignNormalizations

theorem provesFiniteSetAdmissible
    (pkg : SourceObjectPackage) :
    (pkg.toFiniteVanishingCriterionPackage).finiteSetAdmissible :=
  SourceFiniteVanishingCriterionPackage.finite_set_admissible_of_source_package
    pkg.cc20RHExit.sourceFiniteVanishingCriterionPackage

theorem provesFiniteVanishingCriterion
    (pkg : SourceObjectPackage)
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity) :
    RH :=
  (pkg.toFiniteVanishingCriterionPackage).criterion
    input htriple hpositive

theorem finiteVanishingCriterion_factors_through_source_rh
    (pkg : SourceObjectPackage)
    (input : WeilPositivityInput)
    (htriple : input.tripleVanishing)
    (hpositive : input.fullWeilPositivity) :
    (pkg.toFiniteVanishingCriterionPackage).criterion
        input htriple hpositive =
      RHDefinitionBridge.source_rh_to_mathlib_rh
        pkg.cc20RHExit.rhDefinitionBridge
        (pkg.cc20RHExit.sourceFiniteVanishingCriterionPackage.sourceCriterion
          input htriple hpositive) :=
  SourceFiniteVanishingCriterionPackage.criterion_factors_through_source_rh
    pkg.cc20RHExit.sourceFiniteVanishingCriterionPackage
    input htriple hpositive

end SourceObjectPackage
end SourceObject
end Source
end ConnesWeilRH
