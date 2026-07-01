/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Basic
import ConnesWeilRH.Source.CC20Concrete.TraceScale
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Shared source analytic core

This module introduces the common source-facing analytic objects needed by the
CCM24, CCM25, and CC20 source-model discharges.  It deliberately coexists with
the current `TestFunction := Type` scaffold: the `LegacyTestEquiv` field
connects a genuine source test object to the old carrier, so downstream modules
can migrate one theorem row at a time instead of replacing every route type at
once.
-/

namespace ConnesWeilRH
namespace Source
namespace AnalyticCore

open scoped ArithmeticFunction

/-- Bridge between the new source test object and the legacy `TestFunction`. -/
structure LegacyTestEquiv (Test : Type) where
  encode : Test → TestFunction
  decode : TestFunction → Test
  encode_decode : ∀ F : TestFunction, encode (decode F) = F
  decode_encode : ∀ f : Test, decode (encode f) = f

namespace LegacyTestEquiv

@[simp]
theorem encode_decode_apply {Test : Type} (e : LegacyTestEquiv Test)
    (F : TestFunction) :
    e.encode (e.decode F) = F :=
  e.encode_decode F

@[simp]
theorem decode_encode_apply {Test : Type} (e : LegacyTestEquiv Test)
    (f : Test) :
    e.decode (e.encode f) = f :=
  e.decode_encode f

end LegacyTestEquiv

/--
The shared source test algebra.

`convolutionStar` is the CCM25 half-density square product.  The same object is
also the test whose support is controlled by CCM24 and whose trace amplitude is
read by CC20.
-/
structure SourceTestAlgebra where
  Test : Type
  legacy : LegacyTestEquiv Test
  convolutionStar : Test → Test → Test
  involution : Test → Test
  convolutionSquare : Test → Test := fun g => convolutionStar g g
  convolutionSquare_eq : ∀ g : Test, convolutionSquare g = convolutionStar g g

namespace SourceTestAlgebra

def legacyConvolutionStar (A : SourceTestAlgebra) :
    TestFunction → TestFunction → TestFunction :=
  fun f g => A.legacy.encode
    (A.convolutionStar (A.legacy.decode f) (A.legacy.decode g))

theorem legacy_convolution_star_square
    (A : SourceTestAlgebra) (g : A.Test) :
    A.legacyConvolutionStar (A.legacy.encode g) (A.legacy.encode g) =
      A.legacy.encode (A.convolutionSquare g) := by
  simp [legacyConvolutionStar, A.convolutionSquare_eq g]

end SourceTestAlgebra

/-- Source evaluation and Mellin/pole evaluations for the shared test object. -/
structure SourceEvaluationData (A : SourceTestAlgebra) where
  valueAt : A.Test → ℝ → ℝ
  mellinAt : A.Test → ℂ → ℂ
  poleFunctional : A.Test → ℝ
  polePairing : A.Test → ℝ
  poleFunctional_eq_mellin :
    ∀ F : A.Test,
      poleFunctional F =
        (mellinAt F (Complex.I / 2)).re +
          (mellinAt F (-Complex.I / 2)).re
  polePairing_eq_functional_square :
    ∀ g : A.Test,
      polePairing g = poleFunctional (A.convolutionSquare g)

/-- CCM24-facing support/window data for the shared source tests. -/
structure SourceSupportWindowData (A : SourceTestAlgebra) where
  PlaceSet : Type
  Window : Type
  sourcePlaceSet : PlaceSet
  sourceSupportWindow : Window
  sourceTest : A.Test
  canonicalHilbertModel : PlaceSet → Prop
  scalingActionImplemented : PlaceSet → Prop
  fourierGradingCompatible : PlaceSet → Prop
  supportInWindow : A.Test → Window → Prop
  fourierSupportInWindow : A.Test → Window → Prop
  supportTransported : A.Test → Window → Prop
  convolutionSupportTransported : A.Test → Window → Prop
  windowContainedInLambda : Window → ℝ → Prop
  lambdaCompatible : Window → ℝ → Prop
  boundedComparisonMap : PlaceSet → Prop
  boundedComparisonInverse : PlaceSet → Prop
  soninSpaceComparison : Window → Prop
  fixedWindowExhaustionCompatible : Window → Prop

namespace SourceSupportWindowData

def toSemilocalModelSymbols
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) :
    SemilocalModelSymbols where
  PlaceSet := S.PlaceSet
  Window := S.Window
  Test := A.Test
  canonicalHilbertModel := S.canonicalHilbertModel
  scalingActionImplemented := S.scalingActionImplemented
  fourierGradingCompatible := S.fourierGradingCompatible
  supportInWindow := S.supportInWindow
  fourierSupportInWindow := S.fourierSupportInWindow
  supportTransported := S.supportTransported
  convolutionSupportTransported := S.convolutionSupportTransported
  windowContainedInLambda := S.windowContainedInLambda
  lambdaCompatible := S.lambdaCompatible
  boundedComparisonMap := S.boundedComparisonMap
  boundedComparisonInverse := S.boundedComparisonInverse
  soninSpaceComparison := S.soninSpaceComparison
  fixedWindowExhaustionCompatible := S.fixedWindowExhaustionCompatible

end SourceSupportWindowData

/-- CCM24 semilocal rows over the shared source support/window object. -/
structure SourceSemilocalRows
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) where
  sourceCCM24TestCompatibility : Prop
  sourceCanonicalModelData :
    S.canonicalHilbertModel S.sourcePlaceSet
  sourceSupportInWindowData :
    S.supportInWindow S.sourceTest S.sourceSupportWindow
  sourceFourierSupportInWindowData :
    S.fourierSupportInWindow S.sourceTest S.sourceSupportWindow
  sourceSoninSpaceComparisonData :
    S.soninSpaceComparison S.sourceSupportWindow
  sourceWindowContainedInLambdaData :
    ∀ lambda : ℝ,
      1 < lambda → S.windowContainedInLambda S.sourceSupportWindow lambda
  sourceLambdaCompatibilityBridge :
    ∀ lambda : ℝ,
      S.supportInWindow S.sourceTest S.sourceSupportWindow →
        S.fourierSupportInWindow S.sourceTest S.sourceSupportWindow →
          S.supportTransported S.sourceTest S.sourceSupportWindow →
            S.convolutionSupportTransported S.sourceTest S.sourceSupportWindow →
              S.fixedWindowExhaustionCompatible S.sourceSupportWindow →
                S.windowContainedInLambda S.sourceSupportWindow lambda →
                  S.lambdaCompatible S.sourceSupportWindow lambda
  sourceCanonicalSemilocalModel :
    SemilocalModelSymbols.CanonicalSemilocalModelStatement
      S.toSemilocalModelSymbols
  sourceSupportAndFourierSupportTransport :
    SemilocalModelSymbols.SupportTransportStatement
      S.toSemilocalModelSymbols
  sourceConvolutionSupportTransport : Prop
  sourceWindowLambdaCompatibility : Prop
  sourceBoundedComparisonTraceClassTransport :
    SemilocalModelSymbols.BoundedComparisonStatement
      S.toSemilocalModelSymbols
  sourceFixedWindowSoninExhaustion :
    SemilocalModelSymbols.SoninComparisonStatement
      S.toSemilocalModelSymbols

/--
CCM25 finite-prime source arithmetic over the shared test algebra.

The global/restricted index sets are still finite `Finset ℕ` objects to match
the existing scaffold, but the data records the intended source predicates and
the two-sided exact-support laws before any route layer consumes the sums.
-/
structure SourceFinitePrimeData (A : SourceTestAlgebra) where
  globalPrimeIndexSet : Finset ℕ
  restrictedPrimeIndexSet : ℝ → Finset ℕ
  sourcePrimePowerIndex : ℕ → Prop
  sourceAtomVisible : ℕ → A.Test → Prop
  finitePrimeTerm : ℕ → A.Test → ℝ
  primePowerPairing : ℕ → A.Test → A.Test → ℝ
  vonMangoldtWeight : ℕ → ℝ
  vonMangoldtWeight_eq_source :
    ∀ n : ℕ, vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n
  globalExact :
    ∀ F : A.Test, ∀ n : ℕ,
      n ∈ globalPrimeIndexSet ↔
        sourcePrimePowerIndex n ∧ sourceAtomVisible n F
  restrictedExact :
    ∀ lambda : ℝ, ∀ F : A.Test, ∀ n : ℕ,
      n ∈ restrictedPrimeIndexSet lambda ↔
        sourcePrimePowerIndex n ∧ sourceAtomVisible n F ∧
          1 < n ∧ (n : ℝ) ≤ lambda ^ 2
  globalCoverage :
    ∀ F : A.Test, ∀ n : ℕ,
      sourceAtomVisible n F → n ∈ globalPrimeIndexSet
  restrictedCoverage :
    ∀ lambda : ℝ, 1 < lambda → ∀ F : A.Test, ∀ n : ℕ,
      sourceAtomVisible n F → n ∈ restrictedPrimeIndexSet lambda
  termNormalization :
    ∀ f g : A.Test, ∀ n : ℕ,
      finitePrimeTerm n (A.convolutionStar f g) =
        vonMangoldtWeight n * primePowerPairing n f g

namespace SourceFinitePrimeData

def legacyGlobalPrimeIndexSet
    {A : SourceTestAlgebra} (P : SourceFinitePrimeData A) :
    Finset ℕ :=
  P.globalPrimeIndexSet

def legacyRestrictedPrimeIndexSet
    {A : SourceTestAlgebra} (P : SourceFinitePrimeData A) :
    ℝ → Finset ℕ :=
  P.restrictedPrimeIndexSet

def legacyFinitePrimeAtomVisible
    {A : SourceTestAlgebra} (P : SourceFinitePrimeData A) :
    ℕ → TestFunction → Prop :=
  fun n F => P.sourceAtomVisible n (A.legacy.decode F)

def legacyFinitePrimeTerm
    {A : SourceTestAlgebra} (P : SourceFinitePrimeData A) :
    ℕ → TestFunction → ℝ :=
  fun n F => P.finitePrimeTerm n (A.legacy.decode F)

def legacyPrimePowerPairing
    {A : SourceTestAlgebra} (P : SourceFinitePrimeData A) :
    ℕ → TestFunction → TestFunction → ℝ :=
  fun n f g =>
    P.primePowerPairing n (A.legacy.decode f) (A.legacy.decode g)

end SourceFinitePrimeData

/-- CCM25 global/restricted Weil-form formulas over the shared source algebra. -/
structure SourceWeilFormData (A : SourceTestAlgebra) where
  evaluation : SourceEvaluationData A
  finitePrime : SourceFinitePrimeData A
  qw : A.Test → A.Test → ℝ
  qwLambda : ℝ → A.Test → A.Test → ℝ
  psi : A.Test → ℝ
  archimedeanTerm : A.Test → ℝ
  qwDefinition :
    ∀ f g : A.Test, qw f g = psi (A.convolutionStar f g)
  psiSign :
    ∀ F : A.Test,
      psi F =
        evaluation.poleFunctional F - archimedeanTerm F -
          ∑ n ∈ finitePrime.globalPrimeIndexSet,
            finitePrime.finitePrimeTerm n F
  qwLambdaFormula :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ g : A.Test,
        qwLambda lambda g g =
          archimedeanTerm (A.convolutionStar g g) +
            evaluation.polePairing g -
              ∑ n ∈ finitePrime.restrictedPrimeIndexSet lambda,
                finitePrime.vonMangoldtWeight n *
                  finitePrime.primePowerPairing n g g

namespace SourceWeilFormData

def toWeilFormSymbols
    {A : SourceTestAlgebra} (W : SourceWeilFormData A) :
    WeilFormSymbols where
  qw := fun f g => W.qw (A.legacy.decode f) (A.legacy.decode g)
  qwLambda := fun lambda f g =>
    W.qwLambda lambda (A.legacy.decode f) (A.legacy.decode g)
  psi := fun F => W.psi (A.legacy.decode F)
  convolutionStar := A.legacyConvolutionStar
  globalPrimeIndexSet := W.finitePrime.globalPrimeIndexSet
  restrictedPrimeIndexSet := W.finitePrime.restrictedPrimeIndexSet
  finitePrimeAtomVisible :=
    W.finitePrime.legacyFinitePrimeAtomVisible
  finitePrimeTerm := W.finitePrime.legacyFinitePrimeTerm
  archimedeanTerm := fun F => W.archimedeanTerm (A.legacy.decode F)
  poleFunctional := fun F => W.evaluation.poleFunctional (A.legacy.decode F)
  polePairing := fun f => W.evaluation.polePairing (A.legacy.decode f)
  primePowerPairing := W.finitePrime.legacyPrimePowerPairing
  vonMangoldtWeight := W.finitePrime.vonMangoldtWeight

theorem qw_definition_statement
    {A : SourceTestAlgebra} (W : SourceWeilFormData A) :
    WeilFormSymbols.QWDefinitionStatement W.toWeilFormSymbols := by
  intro f g
  simp [toWeilFormSymbols, SourceTestAlgebra.legacyConvolutionStar,
    W.qwDefinition]

theorem psi_sign_statement
    {A : SourceTestAlgebra} (W : SourceWeilFormData A) :
    WeilFormSymbols.PsiSignStatement W.toWeilFormSymbols := by
  intro F
  simpa [toWeilFormSymbols, SourceFinitePrimeData.legacyFinitePrimeTerm]
    using W.psiSign (A.legacy.decode F)

theorem qw_lambda_formula_statement
    {A : SourceTestAlgebra} (W : SourceWeilFormData A) :
    WeilFormSymbols.QWLambdaFormulaStatement W.toWeilFormSymbols := by
  intro lambda hlambda f
  simpa [toWeilFormSymbols, SourceTestAlgebra.legacyConvolutionStar,
    SourceFinitePrimeData.legacyPrimePowerPairing]
    using W.qwLambdaFormula lambda hlambda (A.legacy.decode f)

theorem finite_prime_term_normalization_statement
    {A : SourceTestAlgebra} (W : SourceWeilFormData A) :
    WeilFormSymbols.FinitePrimeNormalizationStatement W.toWeilFormSymbols := by
  intro f g
  refine
    { globalPrimeIndexCoverage := ?_
      restrictedPrimeIndexCoverage := ?_
      finitePrimeTermNormalization := ?_ }
  · intro n hn
    exact W.finitePrime.globalCoverage
      (A.legacy.decode (W.toWeilFormSymbols.convolutionStar f g)) n hn
  · intro lambda hlambda n hn
    exact W.finitePrime.restrictedCoverage lambda hlambda
      (A.legacy.decode (W.toWeilFormSymbols.convolutionStar f g)) n hn
  · intro n
    simpa [toWeilFormSymbols, SourceTestAlgebra.legacyConvolutionStar,
      SourceFinitePrimeData.legacyFinitePrimeTerm,
      SourceFinitePrimeData.legacyPrimePowerPairing]
      using W.finitePrime.termNormalization
        (A.legacy.decode f) (A.legacy.decode g) n

theorem pole_normalization_statement
    {A : SourceTestAlgebra} (W : SourceWeilFormData A) :
    WeilFormSymbols.PoleNormalizationStatement W.toWeilFormSymbols := by
  intro f
  calc
    W.toWeilFormSymbols.polePairing f =
        W.evaluation.poleFunctional (A.convolutionSquare (A.legacy.decode f)) :=
      W.evaluation.polePairing_eq_functional_square (A.legacy.decode f)
    _ = W.toWeilFormSymbols.poleFunctional
        (W.toWeilFormSymbols.convolutionStar f f) := by
      simp [toWeilFormSymbols, SourceTestAlgebra.legacyConvolutionStar,
        A.convolutionSquare_eq (A.legacy.decode f)]

end SourceWeilFormData

/-- CC20 trace-scale source data over the shared test object. -/
structure SourceTraceScaleData (A : SourceTestAlgebra) where
  traceAmplitude : A.Test → ℝ
  traceClass : A.Test → Prop
  cyclicLegal : A.Test → Prop
  hilbertSchmidtGate : A.Test → Prop
  supportSquareTrace : A.Test → ℝ
  sourceNoDefectTrace : A.Test → ℝ
  positiveTrace : A.Test → ℝ
  supportSquareTrace_eq_amplitude_sq :
    ∀ g : A.Test, supportSquareTrace g = traceAmplitude g ^ 2
  positiveTrace_eq_supportSquare :
    ∀ g : A.Test, positiveTrace g = supportSquareTrace g
  traceClass_of_hilbertSchmidt :
    ∀ g : A.Test, hilbertSchmidtGate g → traceClass g
  cyclicLegal_of_hilbertSchmidt :
    ∀ g : A.Test, hilbertSchmidtGate g → cyclicLegal g

namespace SourceTraceScaleData

def toNormalizedLegalSquareTraceScaleSymbols
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A) :
    CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols where
  Test := A.Test
  traceAmplitude := T.traceAmplitude
  traceClass := T.traceClass
  cyclicLegal := T.cyclicLegal

def toArchimedeanTraceSymbols
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A) :
    ArchimedeanTraceSymbols where
  Test := A.Test
  supportSquareTrace := T.supportSquareTrace
  sourceNoDefectTrace := T.sourceNoDefectTrace
  positiveTrace := T.positiveTrace
  traceClass := T.traceClass
  cyclicLegal := T.cyclicLegal
  hilbertSchmidtGate := T.hilbertSchmidtGate
  mellinHalfDensityMatched := True
  uInfinityNormalized := True
  qduNormalized := True
  archimedeanSignNormalized := True

end SourceTraceScaleData

/-- The shared core object consumed by CCM24, CCM25, and CC20. -/
structure SourceAnalyticCore where
  testAlgebra : SourceTestAlgebra
  evaluation : SourceEvaluationData testAlgebra
  supportWindow : SourceSupportWindowData testAlgebra
  weilForm : SourceWeilFormData testAlgebra
  traceScale : SourceTraceScaleData testAlgebra
  weilForm_uses_evaluation : weilForm.evaluation = evaluation

namespace SourceAnalyticCore

def toWeilFormSymbols (core : SourceAnalyticCore) : WeilFormSymbols :=
  core.weilForm.toWeilFormSymbols

def toSemilocalModelSymbols (core : SourceAnalyticCore) :
    SemilocalModelSymbols :=
  core.supportWindow.toSemilocalModelSymbols

def toArchimedeanTraceSymbols (core : SourceAnalyticCore) :
    ArchimedeanTraceSymbols :=
  core.traceScale.toArchimedeanTraceSymbols

def toNormalizedLegalSquareTraceScaleSymbols
    (core : SourceAnalyticCore) :
    CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols :=
  core.traceScale.toNormalizedLegalSquareTraceScaleSymbols

end SourceAnalyticCore

end AnalyticCore
end Source
end ConnesWeilRH
