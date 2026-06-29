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
    (CCM25Concrete.Rows.finite_prime_normalization_of_arithmetic_rows
      pkg.ccm25.concreteArithmeticRows f g).2.2

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
