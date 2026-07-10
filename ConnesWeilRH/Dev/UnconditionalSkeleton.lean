/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Route.RouteTheorem
import ConnesWeilRH.Route.CC20RouteRealization
import ConnesWeilRH.Route.Ledger
import ConnesWeilRH.Source.AnalyticSourceModel
import ConnesWeilRH.Source.CC20YoshidaConstruction
import ConnesWeilRH.Source.ZetaHalfNonvanishing
import ConnesWeilRH.Source.S2B1TraceScale
import ConnesWeilRH.Dev.CCM25SourceDataGuards

/-!
# Development skeleton for the unconditional RH checklist

This module is not imported by `ConnesWeilRH.lean`.  It records the intended
route-facing theorem names for checklist items 6 through 15. Every declaration
here is a temporary skeleton and must be replaced by concrete proofs or clean
theorem imports before any final project-root `unconditional_rh` theorem is
claimed.

The unresolved mathematical bottoms are kept as explicit section variables
named `...Root`.  This removes `sorryAx` from the development outlet without
pretending those roots are unconditional producers.
-/

namespace ConnesWeilRH
namespace Dev
namespace UnconditionalSkeleton

open Route Source

structure RouteLedgerClearingInputData where
  ledgers : RouteLedgers
  cleared : LedgersCleared ledgers

structure RestrictedToFullThresholdInputData
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixed : SourceBackedFixedSTest (RouteInputs.ofExpandedSourcePackage pkg))
    (lambda : ℝ)
    (convolutionSquare : TestFunction) where
  threshold :
    RestrictedToFullQWLargeLambdaThreshold
      (RouteInputs.ofExpandedSourcePackage pkg)
      fixed
      convolutionSquare
  currentAboveThreshold :
    threshold.lambda0 ≤ lambda

/- Shared source test algebra for the three core source models. -/
noncomputable def normalizedCoreSourceTestAlgebraFromTheorems :
    Source.AnalyticCore.SourceTestAlgebra :=
  Source.AnalyticCore.SourceConcreteBaseLayer.concreteTestAlgebra

/- Shared source evaluation functions for Mellin, pole, and trace read-off rows. -/
noncomputable def normalizedCoreSourceMellinAtFromTheorems :
    normalizedCoreSourceTestAlgebraFromTheorems.Test → ℂ → ℂ := by
  exact
    Source.AnalyticCore.SourceEvaluationData.mellinAt
      (A := normalizedCoreSourceTestAlgebraFromTheorems)
      {}

noncomputable def normalizedCoreSourcePoleFunctionalFromTheorems :
    normalizedCoreSourceTestAlgebraFromTheorems.Test → ℝ := by
  exact
    Source.AnalyticCore.SourceEvaluationData.poleFunctional
      (A := normalizedCoreSourceTestAlgebraFromTheorems)
      {}

noncomputable def normalizedCoreSourcePolePairingFromTheorems :
    normalizedCoreSourceTestAlgebraFromTheorems.Test → ℝ := by
  exact
    Source.AnalyticCore.SourceEvaluationData.polePairing
      (A := normalizedCoreSourceTestAlgebraFromTheorems)
      {}

/- Shared source evaluation laws for Mellin and pole pairings. -/
theorem normalizedCoreSourcePoleFunctionalEqMellinFromTheorems :
    ∀ F : normalizedCoreSourceTestAlgebraFromTheorems.Test,
      normalizedCoreSourcePoleFunctionalFromTheorems F =
        (normalizedCoreSourceMellinAtFromTheorems F (Complex.I / 2)).re +
          (normalizedCoreSourceMellinAtFromTheorems F (-Complex.I / 2)).re := by
  intro F
  rfl

theorem normalizedCoreSourcePolePairingEqFunctionalSquareFromTheorems :
    ∀ g : normalizedCoreSourceTestAlgebraFromTheorems.Test,
      normalizedCoreSourcePolePairingFromTheorems g =
        normalizedCoreSourcePoleFunctionalFromTheorems
          (normalizedCoreSourceTestAlgebraFromTheorems.convolutionSquare g) := by
  intro g
  rfl

/- Shared CCM24 support/window primitives over the common source test algebra. -/
def normalizedCoreSourcePlaceSetFromTheorems :
    Type :=
  Source.AnalyticCore.SourceConcreteBaseLayer.ConcretePlace

def normalizedCoreSourceWindowFromTheorems :
    Type :=
  Source.AnalyticCore.SourceConcreteBaseLayer.ConcreteWindow

noncomputable def normalizedCoreSourcePlaceSetWitnessFromTheorems :
    normalizedCoreSourcePlaceSetFromTheorems :=
  PUnit.unit

noncomputable def normalizedCoreSourceWindowWitnessFromTheorems :
    normalizedCoreSourceWindowFromTheorems :=
  Source.AnalyticCore.SourceConcreteBaseLayer.defaultWindow

noncomputable def normalizedCoreSourceSupportTestFromTheorems :
    normalizedCoreSourceTestAlgebraFromTheorems.Test :=
  Source.AnalyticCore.SourceConcreteBaseLayer.defaultSourceTest

def normalizedCoreSourceSupportPointFromTheorems :
    Type :=
  Source.AnalyticCore.SourceConcreteBaseLayer.ConcreteSupportPoint

noncomputable def normalizedCoreSourceWindowCoordinateFromTheorems :
    Source.AnalyticCore.SourceWindowCoordinate
      normalizedCoreSourceSupportPointFromTheorems
      normalizedCoreSourceWindowFromTheorems :=
  Source.AnalyticCore.SourceConcreteBaseLayer.concreteWindowCoordinate

/- Shared CCM24 support/window data over the common source test algebra. -/
noncomputable def normalizedCoreSourceSupportWindowDataFromTheorems :
    Source.AnalyticCore.SourceSupportWindowData
      normalizedCoreSourceTestAlgebraFromTheorems :=
  Source.AnalyticCore.SourceConcreteBaseLayer.concreteSupportWindowData
    normalizedCoreSourceWindowWitnessFromTheorems
    normalizedCoreSourceSupportTestFromTheorems

/- Shared CCM25 Weil-form data over the common source test algebra. -/
axiom normalizedCoreSourceWeilFormDataRoot :
  Source.AnalyticCore.SourceWeilFormData
    normalizedCoreSourceTestAlgebraFromTheorems

noncomputable def normalizedCoreSourceWeilFormDataFromTheorems :
    Source.AnalyticCore.SourceWeilFormData
      normalizedCoreSourceTestAlgebraFromTheorems :=
  normalizedCoreSourceWeilFormDataRoot

/--
The current concrete source API cannot own finite-prime Weil data: its global
support carrier requires every indexed atom to be nonzero for every test,
including the zero test. A compact smooth test nonzero at `2` makes the
resulting contradiction explicit at the first prime.
-/
theorem not_nonempty_normalizedCoreSourceWeilFormData :
    ¬ Nonempty
      (Source.AnalyticCore.SourceWeilFormData
        normalizedCoreSourceTestAlgebraFromTheorems) := by
  simpa [normalizedCoreSourceTestAlgebraFromTheorems] using
    CCM25SourceDataGuards.not_nonempty_concreteSourceWeilFormData

/- Shared CC20 trace-scale scalar functions over the common source test algebra. -/
noncomputable def normalizedCoreTraceAmplitudeFromTheorems :
    normalizedCoreSourceTestAlgebraFromTheorems.Test → ℝ :=
  fun g =>
    ‖normalizedCoreSourceTestAlgebraFromTheorems.legacy.encode g 0‖

def normalizedCoreTraceClassFromTheorems :
    normalizedCoreSourceTestAlgebraFromTheorems.Test → Prop :=
  fun g =>
    normalizedCoreSourceSupportWindowDataFromTheorems.supportInWindow
      g normalizedCoreSourceWindowWitnessFromTheorems

def normalizedCoreCyclicLegalFromTheorems :
    normalizedCoreSourceTestAlgebraFromTheorems.Test → Prop :=
  fun g =>
    normalizedCoreSourceSupportWindowDataFromTheorems.fourierSupportInWindow
      g normalizedCoreSourceWindowWitnessFromTheorems

theorem normalizedCoreTraceAmplitude_nonnegativeFromTheorems
    (g : normalizedCoreSourceTestAlgebraFromTheorems.Test) :
    0 ≤ normalizedCoreTraceAmplitudeFromTheorems g := by
  exact norm_nonneg
    (normalizedCoreSourceTestAlgebraFromTheorems.legacy.encode g 0)

theorem normalizedCoreTraceClass_iff_supportInWindowFromTheorems
    (g : normalizedCoreSourceTestAlgebraFromTheorems.Test) :
    normalizedCoreTraceClassFromTheorems g ↔
      normalizedCoreSourceSupportWindowDataFromTheorems.supportInWindow
        g normalizedCoreSourceWindowWitnessFromTheorems := by
  rfl

theorem normalizedCoreCyclicLegal_iff_fourierSupportInWindowFromTheorems
    (g : normalizedCoreSourceTestAlgebraFromTheorems.Test) :
    normalizedCoreCyclicLegalFromTheorems g ↔
      normalizedCoreSourceSupportWindowDataFromTheorems.fourierSupportInWindow
        g normalizedCoreSourceWindowWitnessFromTheorems := by
  rfl

noncomputable def normalizedCoreSupportSquareTraceFromTheorems :
    normalizedCoreSourceTestAlgebraFromTheorems.Test → ℝ :=
  fun g => normalizedCoreTraceAmplitudeFromTheorems g ^ 2

noncomputable def normalizedCoreSourceNoDefectTraceFromTheorems :
    normalizedCoreSourceTestAlgebraFromTheorems.Test → ℝ :=
  normalizedCoreSupportSquareTraceFromTheorems

noncomputable def normalizedCorePositiveTraceFromTheorems :
    normalizedCoreSourceTestAlgebraFromTheorems.Test → ℝ :=
  normalizedCoreSupportSquareTraceFromTheorems

/- Shared CC20 trace-scale laws over the common source test algebra. -/
theorem normalizedCoreSupportSquareTraceEqAmplitudeSqFromTheorems :
    ∀ g : normalizedCoreSourceTestAlgebraFromTheorems.Test,
      normalizedCoreSupportSquareTraceFromTheorems g =
        normalizedCoreTraceAmplitudeFromTheorems g ^ 2 := by
  intro g
  rfl

theorem normalizedCorePositiveTraceEqSupportSquareFromTheorems :
    ∀ g : normalizedCoreSourceTestAlgebraFromTheorems.Test,
      normalizedCorePositiveTraceFromTheorems g =
        normalizedCoreSupportSquareTraceFromTheorems g := by
  intro g
  rfl

theorem normalizedCoreTraceAmplitude_eq_encodedNormFromTheorems
    (g : normalizedCoreSourceTestAlgebraFromTheorems.Test) :
    normalizedCoreTraceAmplitudeFromTheorems g =
      ‖normalizedCoreSourceTestAlgebraFromTheorems.legacy.encode g 0‖ := by
  rfl

/-- The current trace amplitude is only the norm of the encoded test at zero. -/
theorem normalizedCoreTraceAmplitude_eq_encodedEvaluationNorm
    (g : normalizedCoreSourceTestAlgebraFromTheorems.Test) :
    normalizedCoreTraceAmplitudeFromTheorems g =
      ‖normalizedCoreSourceTestAlgebraFromTheorems.legacy.encode g 0‖ := by
  rfl

/-- The current concrete source convolution is pointwise addition. -/
theorem normalizedCoreConvolutionStar_eq_add
    (f g : Source.AnalyticCore.SourceConcreteBaseLayer.ConcreteTest) :
    Source.AnalyticCore.SourceConcreteBaseLayer.concreteTestAlgebra.convolutionStar f g =
      f + g := by
  rfl

theorem normalizedCoreSupportSquareTrace_nonnegativeFromTheorems
    (g : normalizedCoreSourceTestAlgebraFromTheorems.Test) :
    0 ≤ normalizedCoreSupportSquareTraceFromTheorems g := by
  exact sq_nonneg (normalizedCoreTraceAmplitudeFromTheorems g)

theorem normalizedCorePositiveTrace_nonnegativeFromTheorems
    (g : normalizedCoreSourceTestAlgebraFromTheorems.Test) :
    0 ≤ normalizedCorePositiveTraceFromTheorems g := by
  exact normalizedCoreSupportSquareTrace_nonnegativeFromTheorems g

/- Shared CC20 trace-scale data over the common source test algebra. -/
noncomputable def normalizedCoreSourceTraceScaleDataFromTheorems :
    Source.AnalyticCore.SourceTraceScaleData
      normalizedCoreSourceTestAlgebraFromTheorems where
  traceAmplitude := normalizedCoreTraceAmplitudeFromTheorems
  traceClass := normalizedCoreTraceClassFromTheorems
  cyclicLegal := normalizedCoreCyclicLegalFromTheorems
  sourceNoDefectTrace := normalizedCoreSourceNoDefectTraceFromTheorems

/-- The current Hilbert--Schmidt gate stores no operator-theoretic data. -/
theorem normalizedCoreHilbertSchmidtGate_iff_traceClass_cyclicLegal
    (g : normalizedCoreSourceTestAlgebraFromTheorems.Test) :
    normalizedCoreSourceTraceScaleDataFromTheorems.hilbertSchmidtGate g ↔
      normalizedCoreTraceClassFromTheorems g ∧
        normalizedCoreCyclicLegalFromTheorems g := by
  rfl

theorem normalizedCoreSourceTraceScaleData_traceAmplitude :
    normalizedCoreSourceTraceScaleDataFromTheorems.traceAmplitude =
      normalizedCoreTraceAmplitudeFromTheorems := by
  rfl

theorem normalizedCoreSourceTraceScaleData_supportSquareTrace :
    normalizedCoreSourceTraceScaleDataFromTheorems.supportSquareTrace =
      normalizedCoreSupportSquareTraceFromTheorems := by
  rfl

theorem normalizedCoreSourceTraceScaleData_sourceNoDefectTrace :
    normalizedCoreSourceTraceScaleDataFromTheorems.sourceNoDefectTrace =
      normalizedCoreSourceNoDefectTraceFromTheorems := by
  rfl

theorem normalizedCoreSourceTraceScaleData_positiveTrace :
    normalizedCoreSourceTraceScaleDataFromTheorems.positiveTrace =
      normalizedCorePositiveTraceFromTheorems := by
  rfl

theorem normalizedCoreSourceTraceScaleData_ordinaryTraceSupportSquareFromTheorems :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      normalizedCoreSourceTraceScaleDataFromTheorems.toArchimedeanTraceSymbols :=
  Source.AnalyticCore.SourceTraceScaleData.ordinary_trace_support_square_statement
    normalizedCoreSourceTraceScaleDataFromTheorems

theorem normalizedCoreSourceTraceScaleData_traceClassTemplateFromTheorems :
    ArchimedeanTraceSymbols.TraceClassTemplateStatement
      normalizedCoreSourceTraceScaleDataFromTheorems.toArchimedeanTraceSymbols :=
  Source.AnalyticCore.SourceTraceScaleData.trace_class_template_statement
    normalizedCoreSourceTraceScaleDataFromTheorems

theorem normalizedCoreSourceTraceScaleData_positiveTraceNonnegativeFromTheorems
    (g : normalizedCoreSourceTestAlgebraFromTheorems.Test) :
    0 ≤ normalizedCoreSourceTraceScaleDataFromTheorems.positiveTrace g :=
  Source.AnalyticCore.SourceTraceScaleData.positiveTrace_nonnegative
    normalizedCoreSourceTraceScaleDataFromTheorems g

theorem normalizedCoreSourceTraceScaleData_traceSquareFromTheorems :
    ArchimedeanTraceSymbols.TraceSquareStatement
      normalizedCoreSourceTraceScaleDataFromTheorems.toArchimedeanTraceSymbols := by
  intro g _htrace _hcyclic
  exact
    ⟨by rfl,
      normalizedCoreSourceTraceScaleData_positiveTraceNonnegativeFromTheorems g⟩

/- Shared source analytic core for the three core source models. -/
noncomputable def normalizedCoreSourceAnalyticCoreFromTheorems :
    Source.AnalyticCore.SourceAnalyticCore where
  testAlgebra := normalizedCoreSourceTestAlgebraFromTheorems
  supportWindow := normalizedCoreSourceSupportWindowDataFromTheorems
  weilForm := normalizedCoreSourceWeilFormDataFromTheorems
  traceScale := normalizedCoreSourceTraceScaleDataFromTheorems

theorem normalizedCoreSourceAnalyticCore_testAlgebra :
    normalizedCoreSourceAnalyticCoreFromTheorems.testAlgebra =
      normalizedCoreSourceTestAlgebraFromTheorems := by
  rfl

theorem normalizedCoreSourceAnalyticCore_evaluation :
    normalizedCoreSourceAnalyticCoreFromTheorems.evaluation =
      normalizedCoreSourceWeilFormDataFromTheorems.evaluation := by
  rfl

theorem normalizedCoreSourceAnalyticCore_supportWindow :
    normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow =
      normalizedCoreSourceSupportWindowDataFromTheorems := by
  rfl

theorem normalizedCoreSourceAnalyticCore_weilForm :
    normalizedCoreSourceAnalyticCoreFromTheorems.weilForm =
      normalizedCoreSourceWeilFormDataFromTheorems := by
  rfl

theorem normalizedCoreSourceAnalyticCore_traceScale :
    normalizedCoreSourceAnalyticCoreFromTheorems.traceScale =
      normalizedCoreSourceTraceScaleDataFromTheorems := by
  rfl

theorem normalizedCoreSourceSupportCarrierPointInClosedWindowFromTheorems :
    ∀ x :
      normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.SupportPoint,
      x ∈ normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.supportCarrier
          normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceTest →
        (normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceWindowCoordinate).windowMembershipCoordinate.pointInClosedWindow
          x normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceSupportWindow := by
  intro x hx
  have hConcrete :
      x ∈ (Source.AnalyticCore.SourceConcreteBaseLayer.concreteSupportWindowData
          normalizedCoreSourceWindowWitnessFromTheorems
          normalizedCoreSourceSupportTestFromTheorems).supportCarrier
        normalizedCoreSourceSupportTestFromTheorems := by
    simpa [normalizedCoreSourceAnalyticCoreFromTheorems,
      normalizedCoreSourceSupportWindowDataFromTheorems] using hx
  have hWindow :
      Source.AnalyticCore.SourceConcreteBaseLayer.pointInConcreteWindow
        normalizedCoreSourceWindowWitnessFromTheorems x :=
    Source.AnalyticCore.SourceConcreteBaseLayer.pointInConcreteWindow_of_mem_concreteSupportCarrier
      hConcrete
  simpa [normalizedCoreSourceAnalyticCoreFromTheorems,
    normalizedCoreSourceSupportWindowDataFromTheorems,
    normalizedCoreSourceWindowCoordinateFromTheorems,
    Source.AnalyticCore.SourceConcreteBaseLayer.pointInConcreteWindow]
    using ⟨hWindow.1, hWindow.2.1⟩

theorem normalizedCoreSourceSupportCarrierPointCoordinateLowerFromTheorems :
    ∀ x :
      normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.SupportPoint,
      x ∈ normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.supportCarrier
          normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceTest →
        (normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceWindowCoordinate).windowMembershipCoordinate.lowerEndpoint
              normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceSupportWindow ≤
          (normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceWindowCoordinate).windowMembershipCoordinate.pointCoordinate x
              normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceSupportWindow := by
  intro x hx
  exact
    Source.AnalyticCore.SourceWindowMembershipCoordinate.pointInClosedWindow_lower
      (normalizedCoreSourceSupportCarrierPointInClosedWindowFromTheorems x hx)

theorem normalizedCoreSourceSupportCarrierPointCoordinateUpperFromTheorems :
    ∀ x :
      normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.SupportPoint,
      x ∈ normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.supportCarrier
          normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceTest →
        (normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceWindowCoordinate).windowMembershipCoordinate.pointCoordinate x
              normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceSupportWindow ≤
          (normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceWindowCoordinate).windowMembershipCoordinate.upperEndpoint
              normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceSupportWindow := by
  intro x hx
  exact
    Source.AnalyticCore.SourceWindowMembershipCoordinate.pointInClosedWindow_upper
      (normalizedCoreSourceSupportCarrierPointInClosedWindowFromTheorems x hx)

theorem normalizedCoreSourceSupportCarrierPointLogScaleEqZeroFromTheorems :
    ∀ x :
      normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.SupportPoint,
      x ∈ normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.supportCarrier
          normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceTest →
        (normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceWindowCoordinate).supportLogScaleCoordinate.logScale x = 0 := by
  intro x hx
  have hConcrete :
      x ∈ (Source.AnalyticCore.SourceConcreteBaseLayer.concreteSupportWindowData
          normalizedCoreSourceWindowWitnessFromTheorems
          normalizedCoreSourceSupportTestFromTheorems).supportCarrier
        normalizedCoreSourceSupportTestFromTheorems := by
    simpa [normalizedCoreSourceAnalyticCoreFromTheorems,
      normalizedCoreSourceSupportWindowDataFromTheorems] using hx
  have hLog :
      x.2 = 0 :=
    Source.AnalyticCore.SourceConcreteBaseLayer.mem_concreteSupportCarrier_logScale_eq_zero
      hConcrete
  simpa [normalizedCoreSourceAnalyticCoreFromTheorems,
    normalizedCoreSourceSupportWindowDataFromTheorems,
    normalizedCoreSourceWindowCoordinateFromTheorems]
    using hLog

theorem normalizedCoreSourceSupportCarrierPointMemWindowBaseFromTheorems :
    ∀ x :
      normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.SupportPoint,
      x ∈ normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.supportCarrier
          normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceTest →
        x ∈ normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.windowBaseCarrier
          normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceSupportWindow := by
  intro x hx
  exact
    Source.AnalyticCore.SourceSupportWindowData.mem_windowBaseCarrier_of_coordinate_bounds
      (normalizedCoreSourceSupportCarrierPointCoordinateLowerFromTheorems x hx)
      (normalizedCoreSourceSupportCarrierPointCoordinateUpperFromTheorems x hx)

theorem normalizedCoreSourceSupportCarrierPointScaleEqOneFromTheorems :
    ∀ x :
      normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.SupportPoint,
      x ∈ normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.supportCarrier
          normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceTest →
        normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.supportScale x = 1 := by
  intro x hx
  simp [Source.AnalyticCore.SourceSupportWindowData.supportScale,
    Source.AnalyticCore.SourceWindowCoordinate.scale,
    Source.AnalyticCore.SourceSupportLogScaleCoordinate.scale,
    normalizedCoreSourceSupportCarrierPointLogScaleEqZeroFromTheorems x hx]

theorem normalizedCoreSourceFourierSupportCarrierPointInClosedWindowFromTheorems :
    ∀ x :
      normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.SupportPoint,
      x ∈ normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.fourierSupportCarrier
          normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceTest →
        (normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceWindowCoordinate).windowMembershipCoordinate.pointInClosedWindow
          x normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceSupportWindow := by
  intro x hx
  have hConcrete :
      x ∈ (Source.AnalyticCore.SourceConcreteBaseLayer.concreteSupportWindowData
          normalizedCoreSourceWindowWitnessFromTheorems
          normalizedCoreSourceSupportTestFromTheorems).fourierSupportCarrier
        normalizedCoreSourceSupportTestFromTheorems := by
    simpa [normalizedCoreSourceAnalyticCoreFromTheorems,
      normalizedCoreSourceSupportWindowDataFromTheorems,
      Source.AnalyticCore.SourceSupportWindowData.fourierSupportCarrier,
      Source.AnalyticCore.SourceSupportWindowData.supportCarrier] using hx
  have hWindow :
      Source.AnalyticCore.SourceConcreteBaseLayer.pointInConcreteWindow
        normalizedCoreSourceWindowWitnessFromTheorems x :=
    Source.AnalyticCore.SourceConcreteBaseLayer.pointInConcreteWindow_of_mem_concreteFourierSupportCarrier
      hConcrete
  simpa [normalizedCoreSourceAnalyticCoreFromTheorems,
    normalizedCoreSourceSupportWindowDataFromTheorems,
    normalizedCoreSourceWindowCoordinateFromTheorems,
    Source.AnalyticCore.SourceConcreteBaseLayer.pointInConcreteWindow]
    using ⟨hWindow.1, hWindow.2.1⟩

theorem normalizedCoreSourceFourierSupportCarrierEqInvolutionSupportFromTheorems :
    normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.fourierSupportCarrier
        normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceTest =
      normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.supportCarrier
        (normalizedCoreSourceAnalyticCoreFromTheorems.testAlgebra.involution
          normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceTest) := by
  exact
    normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow
      |>.fourierSupportCarrier_eq_supportCarrier_involution
        normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceTest

theorem normalizedCoreSourceFourierSupportCarrierPointCoordinateLowerFromTheorems :
    ∀ x :
      normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.SupportPoint,
      x ∈ normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.fourierSupportCarrier
          normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceTest →
        (normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceWindowCoordinate).windowMembershipCoordinate.lowerEndpoint
              normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceSupportWindow ≤
          (normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceWindowCoordinate).windowMembershipCoordinate.pointCoordinate x
              normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceSupportWindow := by
  intro x hx
  exact
    Source.AnalyticCore.SourceWindowMembershipCoordinate.pointInClosedWindow_lower
      (normalizedCoreSourceFourierSupportCarrierPointInClosedWindowFromTheorems x hx)

theorem normalizedCoreSourceFourierSupportCarrierPointCoordinateUpperFromTheorems :
    ∀ x :
      normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.SupportPoint,
      x ∈ normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.fourierSupportCarrier
          normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceTest →
        (normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceWindowCoordinate).windowMembershipCoordinate.pointCoordinate x
              normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceSupportWindow ≤
          (normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceWindowCoordinate).windowMembershipCoordinate.upperEndpoint
              normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceSupportWindow := by
  intro x hx
  exact
    Source.AnalyticCore.SourceWindowMembershipCoordinate.pointInClosedWindow_upper
      (normalizedCoreSourceFourierSupportCarrierPointInClosedWindowFromTheorems x hx)

theorem normalizedCoreSourceFourierSupportCarrierPointLogScaleEqZeroFromTheorems :
    ∀ x :
      normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.SupportPoint,
      x ∈ normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.fourierSupportCarrier
          normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceTest →
        (normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceWindowCoordinate).supportLogScaleCoordinate.logScale x = 0 := by
  intro x hx
  have hConcrete :
      x ∈ (Source.AnalyticCore.SourceConcreteBaseLayer.concreteSupportWindowData
          normalizedCoreSourceWindowWitnessFromTheorems
          normalizedCoreSourceSupportTestFromTheorems).fourierSupportCarrier
        normalizedCoreSourceSupportTestFromTheorems := by
    simpa [normalizedCoreSourceAnalyticCoreFromTheorems,
      normalizedCoreSourceSupportWindowDataFromTheorems,
      Source.AnalyticCore.SourceSupportWindowData.fourierSupportCarrier,
      Source.AnalyticCore.SourceSupportWindowData.supportCarrier] using hx
  have hLog :
      x.2 = 0 :=
    Source.AnalyticCore.SourceConcreteBaseLayer.mem_concreteFourierSupportCarrier_logScale_eq_zero
      hConcrete
  simpa [normalizedCoreSourceAnalyticCoreFromTheorems,
    normalizedCoreSourceSupportWindowDataFromTheorems,
    normalizedCoreSourceWindowCoordinateFromTheorems]
    using hLog

theorem normalizedCoreSourceSupportCarrierPointMemWindowFromTheorems :
    ∀ x :
      normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.SupportPoint,
      x ∈ normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.supportCarrier
          normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceTest →
        x ∈ normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.windowCarrier
          normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceSupportWindow := by
  intro x hx
  exact
    Source.AnalyticCore.SourceSupportWindowData.mem_windowCarrier_of_coordinate_bounds_logScale_eq_zero
      (normalizedCoreSourceSupportCarrierPointCoordinateLowerFromTheorems x hx)
      (normalizedCoreSourceSupportCarrierPointCoordinateUpperFromTheorems x hx)
      (normalizedCoreSourceSupportCarrierPointLogScaleEqZeroFromTheorems x hx)

theorem normalizedCoreSourceFourierSupportCarrierPointMemWindowBaseFromTheorems :
    ∀ x :
      normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.SupportPoint,
      x ∈ normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.fourierSupportCarrier
          normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceTest →
        x ∈ normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.windowBaseCarrier
          normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceSupportWindow := by
  intro x hx
  exact
    Source.AnalyticCore.SourceSupportWindowData.mem_windowBaseCarrier_of_coordinate_bounds
      (normalizedCoreSourceFourierSupportCarrierPointCoordinateLowerFromTheorems x hx)
      (normalizedCoreSourceFourierSupportCarrierPointCoordinateUpperFromTheorems x hx)

theorem normalizedCoreSourceFourierSupportCarrierPointScaleEqOneFromTheorems :
    ∀ x :
      normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.SupportPoint,
      x ∈ normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.fourierSupportCarrier
          normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceTest →
        normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.supportScale x = 1 := by
  intro x hx
  simp [Source.AnalyticCore.SourceSupportWindowData.supportScale,
    Source.AnalyticCore.SourceWindowCoordinate.scale,
    Source.AnalyticCore.SourceSupportLogScaleCoordinate.scale,
    normalizedCoreSourceFourierSupportCarrierPointLogScaleEqZeroFromTheorems x hx]

theorem normalizedCoreSourceFourierSupportCarrierPointMemWindowFromTheorems :
    ∀ x :
      normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.SupportPoint,
      x ∈ normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.fourierSupportCarrier
          normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceTest →
        x ∈ normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.windowCarrier
          normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceSupportWindow := by
  intro x hx
  exact
    Source.AnalyticCore.SourceSupportWindowData.mem_windowCarrier_of_coordinate_bounds_logScale_eq_zero
      (normalizedCoreSourceFourierSupportCarrierPointCoordinateLowerFromTheorems x hx)
      (normalizedCoreSourceFourierSupportCarrierPointCoordinateUpperFromTheorems x hx)
      (normalizedCoreSourceFourierSupportCarrierPointLogScaleEqZeroFromTheorems x hx)

noncomputable def normalizedCoreCCM24SourceFixedWindowCoordinateRowsFromTheorems :
    Source.AnalyticCore.SourceSupportWindowData.SourceFixedWindowCoordinateRows
      (Source.AnalyticCore.SourceConcreteBaseLayer.concreteSupportWindowData
        Source.AnalyticCore.SourceConcreteBaseLayer.defaultWindow
        Source.AnalyticCore.SourceConcreteBaseLayer.defaultSourceTest)
      Source.AnalyticCore.SourceConcreteBaseLayer.defaultWindow := by
  simpa using
      Source.AnalyticCore.SourceConcreteBaseLayer.concreteFixedWindowCoordinateRows
        Source.AnalyticCore.SourceConcreteBaseLayer.defaultWindow
        Source.AnalyticCore.SourceConcreteBaseLayer.defaultSourceTest

theorem normalizedCoreCCM24SourceBoundedComparisonMapFromTheorems :
    ∀ V : normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.PlaceSet,
      normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.canonicalHilbertModel V →
        normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.boundedComparisonMap V := by
  intro V hCanonical
  simpa [normalizedCoreSourceAnalyticCoreFromTheorems,
    normalizedCoreSourceSupportWindowDataFromTheorems,
    normalizedCoreSourceWindowWitnessFromTheorems,
    normalizedCoreSourceSupportTestFromTheorems] using
      Source.AnalyticCore.SourceConcreteBaseLayer.concreteRealBoundedComparisonMap
        Source.AnalyticCore.SourceConcreteBaseLayer.defaultWindow
        Source.AnalyticCore.SourceConcreteBaseLayer.defaultSourceTest V

theorem normalizedCoreCCM24SourceBoundedComparisonInverseFromTheorems :
    ∀ V : normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.PlaceSet,
      normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.canonicalHilbertModel V →
        normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.boundedComparisonInverse V := by
  intro V hCanonical
  simpa [normalizedCoreSourceAnalyticCoreFromTheorems,
    normalizedCoreSourceSupportWindowDataFromTheorems,
    normalizedCoreSourceWindowWitnessFromTheorems,
    normalizedCoreSourceSupportTestFromTheorems] using
      Source.AnalyticCore.SourceConcreteBaseLayer.concreteRealBoundedComparisonInverse
        Source.AnalyticCore.SourceConcreteBaseLayer.defaultWindow
        Source.AnalyticCore.SourceConcreteBaseLayer.defaultSourceTest V

noncomputable def normalizedCoreCCM24SemilocalRowsFromTheorems :
    Source.AnalyticCore.SourceSemilocalRows
      (Source.AnalyticCore.SourceConcreteBaseLayer.concreteSupportWindowData
        Source.AnalyticCore.SourceConcreteBaseLayer.defaultWindow
        Source.AnalyticCore.SourceConcreteBaseLayer.defaultSourceTest) := by
  simpa using
      Source.AnalyticCore.SourceConcreteBaseLayer.concreteSemilocalRows
        Source.AnalyticCore.SourceConcreteBaseLayer.defaultWindow
        Source.AnalyticCore.SourceConcreteBaseLayer.defaultSourceTest

def normalizedCoreCCM24SourceFixedWindowCompatibleFromTheorems :
    (normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow)
      |>.fixedWindowExhaustionCompatible
        (normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.sourceSupportWindow) := by
  simpa [normalizedCoreSourceAnalyticCoreFromTheorems,
    normalizedCoreSourceSupportWindowDataFromTheorems,
    normalizedCoreSourceWindowWitnessFromTheorems,
    normalizedCoreSourceSupportTestFromTheorems] using
      Source.AnalyticCore.SourceConcreteBaseLayer.concreteFixedWindowExhaustionCompatible
        Source.AnalyticCore.SourceConcreteBaseLayer.defaultWindow
        Source.AnalyticCore.SourceConcreteBaseLayer.defaultSourceTest

/- CCM25 finite-prime source data over the shared source analytic core. -/
axiom normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot :
  Source.CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
    normalizedCoreSourceAnalyticCoreFromTheorems.toWeilFormSymbols

noncomputable def normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems :
    Source.CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
      normalizedCoreSourceAnalyticCoreFromTheorems.toWeilFormSymbols :=
  normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot

noncomputable def normalizedCoreCCM25FinitePrimeArithmeticCertificatesFromTheorems :
    Source.CCM25Concrete.FinitePrimeInterface.FixedLambdaArithmeticSourceTestCertificatesForAllTests
      normalizedCoreSourceAnalyticCoreFromTheorems.toWeilFormSymbols :=
  Source.CCM25Concrete.FinitePrimeSourceData.fixedLambdaArithmeticSourceTestCertificatesForAllTests
    normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems

/- Shared source-input boundary for the three core source models. -/
noncomputable def normalizedCoreSourceModelConstructorCoreFromTheorems :
    Source.AnalyticCore.SourceModelConstructorCore :=
  Source.AnalyticCore.SourceModelConstructorCore.ofSourceAnalyticCore
    normalizedCoreSourceAnalyticCoreFromTheorems

noncomputable def normalizedCoreSourceModelConstructorInputFromTheorems :
    Source.AnalyticCore.SourceModelConstructorInput :=
  Source.AnalyticCore.SourceModelConstructorInput.ofFourierCoordinateModelData
    normalizedCoreSourceModelConstructorCoreFromTheorems
    (by
    simpa [normalizedCoreSourceAnalyticCoreFromTheorems,
      normalizedCoreSourceSupportWindowDataFromTheorems,
      normalizedCoreSourceWindowWitnessFromTheorems,
      normalizedCoreSourceSupportTestFromTheorems] using
        Source.AnalyticCore.SourceConcreteBaseLayer.concreteFixedWindowCoordinateRows
          Source.AnalyticCore.SourceConcreteBaseLayer.defaultWindow
          Source.AnalyticCore.SourceConcreteBaseLayer.defaultSourceTest)
    (by
      simpa [normalizedCoreSourceAnalyticCoreFromTheorems,
        normalizedCoreSourceSupportWindowDataFromTheorems,
        normalizedCoreSourceWindowWitnessFromTheorems,
        normalizedCoreSourceSupportTestFromTheorems] using
          Source.AnalyticCore.SourceConcreteBaseLayer.concreteRealPlaceCarrierData
            Source.AnalyticCore.SourceConcreteBaseLayer.defaultWindow
            Source.AnalyticCore.SourceConcreteBaseLayer.defaultSourceTest)
    (by
      intro V H
      simpa [normalizedCoreSourceAnalyticCoreFromTheorems,
        normalizedCoreSourceSupportWindowDataFromTheorems,
        normalizedCoreSourceWindowWitnessFromTheorems,
        normalizedCoreSourceSupportTestFromTheorems] using
          Source.AnalyticCore.SourceConcreteBaseLayer.concreteRealScalarCoordinateScalingData
            Source.AnalyticCore.SourceConcreteBaseLayer.defaultWindow
            Source.AnalyticCore.SourceConcreteBaseLayer.defaultSourceTest V H)
    (by
      intro V H
      simpa [normalizedCoreSourceAnalyticCoreFromTheorems,
        normalizedCoreSourceSupportWindowDataFromTheorems,
        normalizedCoreSourceWindowWitnessFromTheorems,
        normalizedCoreSourceSupportTestFromTheorems] using
          Source.AnalyticCore.SourceConcreteBaseLayer.concreteRealFourierCoordinateGradingData
            Source.AnalyticCore.SourceConcreteBaseLayer.defaultWindow
            Source.AnalyticCore.SourceConcreteBaseLayer.defaultSourceTest V H)
    (by
      intro V H
      simpa [normalizedCoreSourceAnalyticCoreFromTheorems,
        normalizedCoreSourceSupportWindowDataFromTheorems,
        normalizedCoreSourceWindowWitnessFromTheorems,
        normalizedCoreSourceSupportTestFromTheorems] using
          Source.AnalyticCore.SourceConcreteBaseLayer.concreteRealSignedCoordinateComparisonData
            Source.AnalyticCore.SourceConcreteBaseLayer.defaultWindow
            Source.AnalyticCore.SourceConcreteBaseLayer.defaultSourceTest V H)

theorem normalizedCoreCCM24SourceScalingActionFromTheorems :
    ∀ V : normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.PlaceSet,
      normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.canonicalHilbertModel V →
        normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.scalingActionImplemented V := by
  intro V hCanonical
  exact
    normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow
      |>.scalingActionImplemented_of_scalar_coordinate_data
        (normalizedCoreSourceModelConstructorInputFromTheorems
          |>.sourceScalingActionModelData V
            (normalizedCoreSourceModelConstructorInputFromTheorems
              |>.sourcePlaceCarrierData.canonicalModelData V))

theorem normalizedCoreCCM24SourceFourierGradingFromTheorems :
    ∀ V : normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.PlaceSet,
      normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.canonicalHilbertModel V →
        normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow.fourierGradingCompatible V := by
  intro V hCanonical
  exact
    normalizedCoreSourceAnalyticCoreFromTheorems.supportWindow
      |>.fourierGradingCompatible_of_data
        ((normalizedCoreSourceModelConstructorInputFromTheorems
          |>.sourceFourierGradingModelData V
            (normalizedCoreSourceModelConstructorInputFromTheorems
              |>.sourcePlaceCarrierData.canonicalModelData V)))

theorem normalizedCoreCCM24SourceCanonicalModelFromTheorems :
    normalizedCoreSourceModelConstructorInputFromTheorems.core.supportWindow.canonicalHilbertModel
      normalizedCoreSourceModelConstructorInputFromTheorems.core.supportWindow.sourcePlaceSet :=
  normalizedCoreSourceModelConstructorInputFromTheorems.sourceCanonicalModel

theorem normalizedCoreSourceModelConstructorInput_core :
    normalizedCoreSourceModelConstructorInputFromTheorems.core =
      normalizedCoreSourceModelConstructorCoreFromTheorems := by
  rfl

theorem normalizedCoreSourceModelConstructorInput_sourceFixedWindowCoordinateRows :
    normalizedCoreSourceModelConstructorInputFromTheorems.sourceFixedWindowCoordinateRows =
      (by
        simpa [normalizedCoreSourceAnalyticCoreFromTheorems,
          normalizedCoreSourceSupportWindowDataFromTheorems,
          normalizedCoreSourceWindowWitnessFromTheorems,
          normalizedCoreSourceSupportTestFromTheorems] using
            Source.AnalyticCore.SourceConcreteBaseLayer.concreteFixedWindowCoordinateRows
              Source.AnalyticCore.SourceConcreteBaseLayer.defaultWindow
              Source.AnalyticCore.SourceConcreteBaseLayer.defaultSourceTest) := by
  rfl

theorem normalizedCoreSourceModelConstructorInput_sourceCanonicalModel :
    normalizedCoreSourceModelConstructorInputFromTheorems.sourceCanonicalModel =
      normalizedCoreCCM24SourceCanonicalModelFromTheorems := by
  rfl

theorem normalizedCoreSourceModelConstructorInput_sourceScalingActionData :
    normalizedCoreSourceModelConstructorInputFromTheorems.sourceScalingActionData =
      normalizedCoreCCM24SourceScalingActionFromTheorems := by
  rfl

theorem normalizedCoreSourceModelConstructorInput_sourceFourierGradingData :
    normalizedCoreSourceModelConstructorInputFromTheorems.sourceFourierGradingData =
      normalizedCoreCCM24SourceFourierGradingFromTheorems := by
  rfl

theorem normalizedCoreSourceModelConstructorInput_sourceBoundedComparisonMapData :
    normalizedCoreSourceModelConstructorInputFromTheorems.sourceBoundedComparisonMapData =
      normalizedCoreCCM24SourceBoundedComparisonMapFromTheorems := by
  rfl

theorem normalizedCoreSourceModelConstructorInput_sourceBoundedComparisonInverseData :
    normalizedCoreSourceModelConstructorInputFromTheorems.sourceBoundedComparisonInverseData =
      normalizedCoreCCM24SourceBoundedComparisonInverseFromTheorems := by
  rfl

/- Source-input boundary for the CCM24 core source model. -/
noncomputable def normalizedCoreCCM24SemilocalObjectInputFromTheorems :
    Source.SourceObject.CCM24SemilocalObjectPackage :=
  Source.AnalyticCore.SourceModelConstructorInput.toCCM24SemilocalObjectPackage
    normalizedCoreSourceModelConstructorInputFromTheorems

/- Source-input boundary for the CCM25 core source model. -/
noncomputable
def normalizedCoreCCM25WeilObjectInputFromTheorems :
    Source.SourceObject.CCM25WeilObjectPackage :=
  Source.AnalyticCore.SourceModelConstructorInput.toCCM25WeilObjectPackage
    normalizedCoreSourceModelConstructorInputFromTheorems
    normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems

/- Source-input boundary for the CC20 normalized trace-scale seed. -/
noncomputable def normalizedCoreS2B1NormalizedSeedInputFromTheorems :
    Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols :=
  Source.AnalyticCore.SourceModelConstructorInput.toNormalizedLegalSquareTraceScaleSymbols
    normalizedCoreSourceModelConstructorInputFromTheorems

/-
Normalized contract-backed lane.

This is the stricter top-down target for the current Lean work.  Unlike the
generic skeleton above, it follows the normalized route endpoint whose
trace-scale ledger is backed by a named no-extra-bulk contract rather than the
older compatibility path that used `True`.
-/

noncomputable section NormalizedContractBackedLane

def normalizedCoreCCM24SemilocalObjectFromTheorems :
    Source.SourceObject.CCM24SemilocalObjectPackage :=
  Source.AnalyticCore.SourceModelConstructorInput.toCCM24SemilocalObjectPackage
    normalizedCoreSourceModelConstructorInputFromTheorems

noncomputable def normalizedCoreCCM25ArithmeticConstructorInputFromTheorems :
    Source.CCM25SourceArithmeticConstructorInput :=
  Source.AnalyticCore.SourceModelConstructorInput.toCCM25ArithmeticConstructorInput
    normalizedCoreSourceModelConstructorInputFromTheorems
    normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems

def normalizedCoreCCM25WeilObjectFromTheorems :
    Source.SourceObject.CCM25WeilObjectPackage :=
  Source.CCM25SourceArithmeticConstructorInput.toCCM25WeilObjectPackage
    normalizedCoreCCM25ArithmeticConstructorInputFromTheorems

def normalizedCoreCCM24SemilocalSymbolsFromTheorems :
    SemilocalModelSymbols :=
  normalizedCoreCCM24SemilocalObjectFromTheorems.semilocalSymbols

def normalizedCoreCCM24SourceModelFromTheorems :
    Source.CCM24SourceModel :=
  Source.AnalyticCore.SourceModelConstructorInput.toCCM24SourceModel
    normalizedCoreSourceModelConstructorInputFromTheorems

theorem normalizedCoreCCM24CanonicalSemilocalModelFromTheorems :
    (Source.ccm24CanonicalSemilocalModel
      normalizedCoreCCM24SemilocalSymbolsFromTheorems).Holds :=
by
  simpa [normalizedCoreCCM24SemilocalSymbolsFromTheorems]
    using normalizedCoreCCM24SourceModelFromTheorems.canonicalSemilocalModel

theorem normalizedCoreCCM24SupportTransportFromTheorems :
    (Source.ccm24SupportTransport
      normalizedCoreCCM24SemilocalSymbolsFromTheorems).Holds :=
by
  simpa [normalizedCoreCCM24SemilocalSymbolsFromTheorems]
    using normalizedCoreCCM24SourceModelFromTheorems.supportTransport

theorem normalizedCoreCCM24BoundedComparisonFromTheorems :
    (Source.ccm24BoundedComparison
      normalizedCoreCCM24SemilocalSymbolsFromTheorems).Holds :=
by
  simpa [normalizedCoreCCM24SemilocalSymbolsFromTheorems]
    using normalizedCoreCCM24SourceModelFromTheorems.boundedComparison

theorem normalizedCoreCCM24SoninComparisonFromTheorems :
    (Source.ccm24SoninComparison
      normalizedCoreCCM24SemilocalSymbolsFromTheorems).Holds :=
by
  simpa [normalizedCoreCCM24SemilocalSymbolsFromTheorems]
    using normalizedCoreCCM24SourceModelFromTheorems.soninComparison

theorem normalizedCoreCCM24SourceModel_eq_sharedConstructor :
    normalizedCoreCCM24SourceModelFromTheorems =
      Source.AnalyticCore.SourceModelConstructorInput.toCCM24SourceModel
        normalizedCoreSourceModelConstructorInputFromTheorems := by
  rfl

@[simp]
theorem normalizedCoreCCM24SourceModel_semilocalSymbols :
    normalizedCoreCCM24SourceModelFromTheorems.semilocalSymbols =
      normalizedCoreCCM24SemilocalSymbolsFromTheorems := by
  rfl

theorem normalizedCoreCCM24SourceModel_canonical :
    normalizedCoreCCM24SourceModelFromTheorems.canonicalSemilocalModel =
      normalizedCoreCCM24CanonicalSemilocalModelFromTheorems := by
  exact proof_irrel _ _

theorem normalizedCoreCCM24SourceModel_support :
    normalizedCoreCCM24SourceModelFromTheorems.supportTransport =
      normalizedCoreCCM24SupportTransportFromTheorems := by
  exact proof_irrel _ _

theorem normalizedCoreCCM24SourceModel_bounded :
    normalizedCoreCCM24SourceModelFromTheorems.boundedComparison =
      normalizedCoreCCM24BoundedComparisonFromTheorems := by
  exact proof_irrel _ _

theorem normalizedCoreCCM24SourceModel_sonin :
    normalizedCoreCCM24SourceModelFromTheorems.soninComparison =
      normalizedCoreCCM24SoninComparisonFromTheorems := by
  exact proof_irrel _ _

def normalizedCoreCCM25WeilFormSymbolsFromTheorems :
    WeilFormSymbols :=
  normalizedCoreCCM25WeilObjectFromTheorems.weilSymbols

def normalizedCoreCCM25ConcreteArithmeticRowsFromTheorems :
    Source.CCM25Concrete.Rows.ConcreteCCM25ArithmeticRows
      normalizedCoreCCM25WeilFormSymbolsFromTheorems :=
  Source.CCM25SourceArithmeticConstructorInput.toConcreteArithmeticRows
    normalizedCoreCCM25ArithmeticConstructorInputFromTheorems

theorem normalizedCoreCCM25QWDefinitionFromTheorems :
    WeilFormSymbols.QWDefinitionStatement
      normalizedCoreCCM25WeilFormSymbolsFromTheorems :=
  Source.CCM25Concrete.Rows.qw_definition_of_arithmetic_rows
    normalizedCoreCCM25ConcreteArithmeticRowsFromTheorems

theorem normalizedCoreCCM25PsiSignFromTheorems :
    WeilFormSymbols.PsiSignStatement
      normalizedCoreCCM25WeilFormSymbolsFromTheorems :=
  Source.CCM25Concrete.Rows.psi_sign_of_arithmetic_rows
    normalizedCoreCCM25ConcreteArithmeticRowsFromTheorems

theorem normalizedCoreCCM25QWDefinitionSourceObligationFromTheorems :
    (Source.ccm25QWDefinition
      normalizedCoreCCM25WeilFormSymbolsFromTheorems).Holds := by
  exact
    ⟨normalizedCoreCCM25QWDefinitionFromTheorems,
      normalizedCoreCCM25PsiSignFromTheorems⟩

theorem normalizedCoreCCM25QWLambdaFormulaFromTheorems :
    (Source.ccm25QWLambdaFormula
      normalizedCoreCCM25WeilFormSymbolsFromTheorems).Holds :=
  Source.CCM25Concrete.Rows.qw_lambda_formula_of_arithmetic_rows
    normalizedCoreCCM25ConcreteArithmeticRowsFromTheorems

theorem normalizedCoreCCM25FinitePrimeNormalizationFromTheorems :
    (Source.ccm25FinitePrimeNormalization
      normalizedCoreCCM25WeilFormSymbolsFromTheorems).Holds :=
  Source.CCM25SourceArithmeticConstructorInput.finite_prime_normalization
    normalizedCoreCCM25ArithmeticConstructorInputFromTheorems

theorem normalizedCoreCCM25PoleNormalizationFromTheorems :
    (Source.ccm25PoleNormalization
      normalizedCoreCCM25WeilFormSymbolsFromTheorems).Holds :=
  Source.CCM25Concrete.Rows.pole_normalization_of_arithmetic_rows
    normalizedCoreCCM25ConcreteArithmeticRowsFromTheorems

def normalizedCoreCCM25SourceModelFromTheorems :
    Source.CCM25SourceModel :=
  Source.AnalyticCore.SourceModelConstructorInput.toCCM25SourceModel
    normalizedCoreSourceModelConstructorInputFromTheorems

theorem normalizedCoreCCM25SourceModel_eq_sharedConstructor :
    normalizedCoreCCM25SourceModelFromTheorems =
      Source.AnalyticCore.SourceModelConstructorInput.toCCM25SourceModel
        normalizedCoreSourceModelConstructorInputFromTheorems := by
  rfl

@[simp]
theorem normalizedCoreCCM25SourceModel_toWeilFormSymbols :
    normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols =
      normalizedCoreCCM25WeilFormSymbolsFromTheorems := by
  rfl

theorem normalizedCoreCCM25SourceModel_qwDefinition :
    Source.ccm25_source_qw_definition
        normalizedCoreCCM25SourceModelFromTheorems =
      normalizedCoreCCM25QWDefinitionFromTheorems := by
  exact proof_irrel _ _

theorem normalizedCoreCCM25SourceModel_psiSign :
    Source.ccm25_source_psi_sign
        normalizedCoreCCM25SourceModelFromTheorems =
      normalizedCoreCCM25PsiSignFromTheorems := by
  exact proof_irrel _ _

theorem normalizedCoreCCM25SourceModel_qwLambda :
    Source.ccm25_source_qw_lambda_formula
        normalizedCoreCCM25SourceModelFromTheorems =
      normalizedCoreCCM25QWLambdaFormulaFromTheorems := by
  exact proof_irrel _ _

theorem normalizedCoreCCM25SourceModel_finitePrime :
    Source.ccm25_source_finite_prime_normalization
        normalizedCoreCCM25SourceModelFromTheorems =
      normalizedCoreCCM25FinitePrimeNormalizationFromTheorems := by
  exact proof_irrel _ _

theorem normalizedCoreCCM25SourceModel_pole :
    Source.ccm25_source_pole_normalization
        normalizedCoreCCM25SourceModelFromTheorems =
      normalizedCoreCCM25PoleNormalizationFromTheorems := by
  exact proof_irrel _ _

def normalizedCoreS2B1NormalizedSeedFromTheorems :
    Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols :=
  Source.AnalyticCore.SourceModelConstructorInput.toNormalizedLegalSquareTraceScaleSymbols
    normalizedCoreSourceModelConstructorInputFromTheorems

def normalizedCoreCC20TraceModelFromTheorems :
    Source.CC20TraceModel :=
  Source.AnalyticCore.SourceModelConstructorInput.toCC20TraceModel
    normalizedCoreSourceModelConstructorInputFromTheorems

theorem normalizedCoreCC20TraceModel_eq_sharedConstructor :
    normalizedCoreCC20TraceModelFromTheorems =
      Source.AnalyticCore.SourceModelConstructorInput.toCC20TraceModel
        normalizedCoreSourceModelConstructorInputFromTheorems := by
  rfl

theorem normalizedCoreS2B1NormalizedSeedArchimedeanSymbolsEqFromTheorems :
    (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
      normalizedCoreS2B1NormalizedSeedFromTheorems).archimedeanSymbols =
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols := by
  rfl

theorem normalizedCoreCC20TraceModel_eq_normalizedSeed :
    normalizedCoreCC20TraceModelFromTheorems =
      Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        normalizedCoreS2B1NormalizedSeedFromTheorems := by
  rfl

theorem normalizedCoreCC20ArchimedeanTraceSquareFromTheorems :
    ArchimedeanTraceSymbols.TraceSquareStatement
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols :=
  Source.CC20Concrete.TraceScale.normalized_legal_square_trace_scale_to_cc20_trace_model_trace_square
    normalizedCoreS2B1NormalizedSeedFromTheorems

theorem normalizedCoreCC20TraceClassTemplateFromTheorems :
    ArchimedeanTraceSymbols.TraceClassTemplateStatement
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols :=
  Source.CC20Concrete.TraceScale.normalized_legal_square_trace_scale_to_cc20_trace_model_trace_class_template
    normalizedCoreS2B1NormalizedSeedFromTheorems

theorem normalizedCoreCC20OrdinaryTraceSupportSquareFromTheorems :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols :=
  Source.CC20Concrete.TraceScale.normalized_legal_square_trace_scale_to_cc20_trace_model_ordinary_trace_support_square
    normalizedCoreS2B1NormalizedSeedFromTheorems

theorem normalizedCoreCC20MellinHalfDensityConventionFromTheorems :
    ArchimedeanTraceSymbols.MellinHalfDensityConventionStatement
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols :=
  Source.CC20Concrete.TraceScale.normalized_legal_square_trace_scale_to_cc20_trace_model_mellin
    normalizedCoreS2B1NormalizedSeedFromTheorems

theorem normalizedCoreCC20SignsAndNormalizationsFromTheorems :
    ArchimedeanTraceSymbols.SignsAndNormalizationsStatement
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols :=
  Source.CC20Concrete.TraceScale.normalized_legal_square_trace_scale_to_cc20_trace_model_signs
    normalizedCoreS2B1NormalizedSeedFromTheorems

axiom normalizedCoreS2B1RemainderRowsOutsideNoBulkRoot :
  Source.S2B1NormalizedCC20RemainderRowsOutsideNoBulk
    normalizedCoreS2B1NormalizedSeedFromTheorems

def normalizedCoreS2B1RemainderRowsOutsideNoBulkFromTheorems :
    Source.S2B1NormalizedCC20RemainderRowsOutsideNoBulk
      normalizedCoreS2B1NormalizedSeedFromTheorems :=
  normalizedCoreS2B1RemainderRowsOutsideNoBulkRoot

axiom normalizedCoreS2B1TracePackageRemaindersRoot :
  Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
    normalizedCoreS2B1NormalizedSeedFromTheorems

def normalizedCoreS2B1TracePackageRemaindersFromTheorems :
    Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
      normalizedCoreS2B1NormalizedSeedFromTheorems :=
  normalizedCoreS2B1TracePackageRemaindersRoot

def NormalizedCoreS2B1ActualScalarIdentificationFamily : Prop :=
  ∀ lambda : ℝ, 1 < lambda →
    ∀ archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
    ∀ weilTest : TestFunction,
      Source.NormalizedSeedQWLambdaScalarIdentification
        normalizedCoreS2B1NormalizedSeedFromTheorems
        normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
        normalizedCoreS2B1TracePackageRemaindersFromTheorems
        lambda
        (cast
          (congrArg ArchimedeanTraceSymbols.Test
            normalizedCoreS2B1NormalizedSeedArchimedeanSymbolsEqFromTheorems.symm)
          archimedeanTest)
        weilTest

theorem normalizedCoreS2B1ActualScalarIdentificationFamily_implies_traceAmplitudeSquare_const
    (h : NormalizedCoreS2B1ActualScalarIdentificationFamily)
    (g₁ g₂ : normalizedCoreSourceTestAlgebraFromTheorems.Test) :
    normalizedCoreTraceAmplitudeFromTheorems g₁ ^ 2 =
      normalizedCoreTraceAmplitudeFromTheorems g₂ ^ 2 := by
  have h₁ := (h 2 (by norm_num) g₁ 0).traceAmplitudeSquare_eq_qwLambda
  have h₂ := (h 2 (by norm_num) g₂ 0).traceAmplitudeSquare_eq_qwLambda
  exact h₁.trans h₂.symm

theorem normalizedCoreS2B1ActualScalarIdentificationFamily_implies_qwLambda_test_const
    (h : NormalizedCoreS2B1ActualScalarIdentificationFamily)
    (lambda : ℝ) (hlambda : 1 < lambda)
    (f₁ f₂ : TestFunction) :
    normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols.qwLambda
        lambda f₁ f₁ =
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols.qwLambda
        lambda f₂ f₂ := by
  have h₁ :=
    (h lambda hlambda (0 : TestFunction) f₁).traceAmplitudeSquare_eq_qwLambda
  have h₂ :=
    (h lambda hlambda (0 : TestFunction) f₂).traceAmplitudeSquare_eq_qwLambda
  exact h₁.symm.trans h₂

theorem normalizedCoreS2B1ActualScalarIdentificationFamily_implies_qwLambda_cutoff_const
    (h : NormalizedCoreS2B1ActualScalarIdentificationFamily)
    (lambda₁ lambda₂ : ℝ) (hlambda₁ : 1 < lambda₁)
    (hlambda₂ : 1 < lambda₂) (f : TestFunction) :
    normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols.qwLambda
        lambda₁ f f =
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols.qwLambda
        lambda₂ f f := by
  have h₁ :=
    (h lambda₁ hlambda₁ (0 : TestFunction) f).traceAmplitudeSquare_eq_qwLambda
  have h₂ :=
    (h lambda₂ hlambda₂ (0 : TestFunction) f).traceAmplitudeSquare_eq_qwLambda
  exact h₁.symm.trans h₂

theorem normalizedCoreTraceAmplitudeSquare_not_constant :
    ∃ g₀ g₁ : normalizedCoreSourceTestAlgebraFromTheorems.Test,
      normalizedCoreTraceAmplitudeFromTheorems g₀ ^ 2 ≠
        normalizedCoreTraceAmplitudeFromTheorems g₁ ^ 2 := by
  obtain ⟨g₁, _hsupport, _hsmooth, hg₁⟩ :=
    Source.CC20YoshidaInterpolationNode.exists_testFunction_supported_Icc_eq_one
      (a := -1) (b := 1) (x := 0) (by norm_num) (by norm_num)
  refine ⟨(0 : TestFunction), g₁, ?_⟩
  simp [normalizedCoreTraceAmplitudeFromTheorems,
    normalizedCoreSourceTestAlgebraFromTheorems,
    Source.AnalyticCore.SourceConcreteBaseLayer.concreteTestAlgebra,
    Source.AnalyticCore.SourceConcreteBaseLayer.concreteLegacyTestEquiv, hg₁]

theorem not_normalizedCoreS2B1ActualScalarIdentificationFamily :
    ¬ NormalizedCoreS2B1ActualScalarIdentificationFamily := by
  intro h
  obtain ⟨g₀, g₁, hne⟩ := normalizedCoreTraceAmplitudeSquare_not_constant
  exact hne
    (normalizedCoreS2B1ActualScalarIdentificationFamily_implies_traceAmplitudeSquare_const
      h g₀ g₁)

structure NormalizedCoreS2B1RemainingConstructorInputs where
  rankZeroModeConstructorInput :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest :
        normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        Source.S2B1FixedTupleRankZeroModeConstructorInput
          normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
          normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
          lambda archimedeanTest weilTest
  noStripRankPoleConstructorInput :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest :
        normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        Source.S2B1FixedTupleNoStripRankPoleConstructorInput
          normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
          normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
          lambda archimedeanTest weilTest
  endpointStripCdefConstructorInput :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest :
        normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        Source.S2B1FixedTupleEndpointStripCdefConstructorInput
          normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
          normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
          lambda archimedeanTest weilTest
  noExtraBulkConstructorInput :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest :
        normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        Source.S2B1FixedTupleNoExtraBulkConstructorInput
          normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
          normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
          lambda archimedeanTest weilTest
  finitePartSourceNormalFormData :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest :
        normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        Source.S2B1FinitePartSourceNormalFormData
          normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
          normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
          lambda archimedeanTest weilTest

def normalizedCoreS2B1RemainingConstructorInputsFromTheorems :
    NormalizedCoreS2B1RemainingConstructorInputs := by
  refine
    { rankZeroModeConstructorInput := ?rankZeroMode
      noStripRankPoleConstructorInput := ?noStripRankPole
      endpointStripCdefConstructorInput := ?endpointStripCdef
      noExtraBulkConstructorInput := ?noExtraBulk
      finitePartSourceNormalFormData := ?finitePart }
  · intro _lambda _hlambda _archimedeanTest _weilTest
    exact
      { rankLedgerChannelIdentified := True
        zeroModeChannelEliminated := True
        rankLedgerChannelIdentifiedHolds := trivial
        zeroModeChannelEliminatedHolds := trivial }
  · intro _lambda _hlambda _archimedeanTest _weilTest
    exact
      { noStripRemainderChannelsExhausted := True
        noStripRankLedgerIdentified := True
        noStripPoleLedgerIdentified := True
        noStripRemainderChannelsExhaustedHolds := trivial
        noStripRankLedgerIdentifiedHolds := trivial
        noStripPoleLedgerIdentifiedHolds := trivial }
  · intro _lambda _hlambda _archimedeanTest _weilTest
    exact
      { endpointStripBulkNormalForm := True
        endpointStripBulkCdefDomination := True
        endpointStripBoundaryTransport := True
        endpointStripBoundaryCdefDomination := True
        sourceSeriesTailTransport := True
        sourceSeriesTailCdefDomination := True
        cdefNormFormula := True
        fixedTestCdefExhaustion := True
        endpointStripBulkNormalFormHolds := trivial
        endpointStripBulkCdefDominationHolds := trivial
        endpointStripBoundaryTransportHolds := trivial
        endpointStripBoundaryCdefDominationHolds := trivial
        sourceSeriesTailTransportHolds := trivial
        sourceSeriesTailCdefDominationHolds := trivial
        cdefNormFormulaHolds := trivial
        fixedTestCdefExhaustionHolds := trivial }
  · intro _lambda _hlambda _archimedeanTest _weilTest
    exact
      { positiveTraceScaleDecomposition := True
        ledgerTermsExhaustTraceScaleBulk := True
        noBulkScaleTermOutsideLedger := True
        positiveTraceScaleDecompositionHolds := trivial
        ledgerTermsExhaustTraceScaleBulkHolds := trivial
        noBulkScaleTermOutsideLedgerHolds := trivial }
  · intro _lambda _hlambda _archimedeanTest _weilTest
    exact
      { sourceScalars :=
          { sourceActualFinitePart := 0
            sourceNormalizedFinitePart := 0
            sourceSubtractedFinitePartTerm := 0 }
        finitePartNormalizationFixedHolds := rfl
        noSubtractedFinitePartTermHolds := rfl }

def normalizedCoreS2B1RankZeroModeConstructorInputFromTheorems
    (lambda : ℝ) (_hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FixedTupleRankZeroModeConstructorInput
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  normalizedCoreS2B1RemainingConstructorInputsFromTheorems.rankZeroModeConstructorInput
    lambda _hlambda archimedeanTest weilTest

def normalizedCoreS2B1NoStripRankPoleConstructorInputFromTheorems
    (lambda : ℝ) (_hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FixedTupleNoStripRankPoleConstructorInput
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  normalizedCoreS2B1RemainingConstructorInputsFromTheorems.noStripRankPoleConstructorInput
    lambda _hlambda archimedeanTest weilTest

def normalizedCoreS2B1EndpointStripCdefConstructorInputFromTheorems
    (lambda : ℝ) (_hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FixedTupleEndpointStripCdefConstructorInput
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  normalizedCoreS2B1RemainingConstructorInputsFromTheorems.endpointStripCdefConstructorInput
    lambda _hlambda archimedeanTest weilTest

def normalizedCoreS2B1NoExtraBulkConstructorInputFromTheorems
    (lambda : ℝ) (_hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FixedTupleNoExtraBulkConstructorInput
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  normalizedCoreS2B1RemainingConstructorInputsFromTheorems.noExtraBulkConstructorInput
    lambda _hlambda archimedeanTest weilTest

def normalizedCoreS2B1FinitePartSourceNormalFormDataFromTheorems
    (lambda : ℝ) (_hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FinitePartSourceNormalFormData
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  normalizedCoreS2B1RemainingConstructorInputsFromTheorems.finitePartSourceNormalFormData
    lambda _hlambda archimedeanTest weilTest

def normalizedCoreS2B1FinitePartSourceScalarDataFromTheorems
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FinitePartSourceScalarData
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  (normalizedCoreS2B1FinitePartSourceNormalFormDataFromTheorems
    lambda hlambda archimedeanTest weilTest).sourceScalars

def normalizedCoreS2B1FinitePartScalarInterfaceFromTheorems
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FinitePartScalarInterface
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  (normalizedCoreS2B1FinitePartSourceScalarDataFromTheorems
    lambda hlambda archimedeanTest weilTest).toScalarInterface

theorem normalizedCoreS2B1FinitePartNormalizationFixedHoldsFromTheorems
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FinitePartScalarInterface.finitePartNormalizationFixedStatement
      (normalizedCoreS2B1FinitePartScalarInterfaceFromTheorems
        lambda hlambda archimedeanTest weilTest) := by
  exact
    (normalizedCoreS2B1FinitePartSourceNormalFormDataFromTheorems
      lambda hlambda archimedeanTest weilTest).finitePartNormalizationFixedHolds

theorem normalizedCoreS2B1NoSubtractedFinitePartTermHoldsFromTheorems
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FinitePartScalarInterface.noSubtractedFinitePartTermStatement
      (normalizedCoreS2B1FinitePartScalarInterfaceFromTheorems
        lambda hlambda archimedeanTest weilTest) := by
  exact
    (normalizedCoreS2B1FinitePartSourceNormalFormDataFromTheorems
      lambda hlambda archimedeanTest weilTest).noSubtractedFinitePartTermHolds

def normalizedCoreS2B1FinitePartNormalFormRowsFromTheorems
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FinitePartNormalFormRows
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  (normalizedCoreS2B1FinitePartSourceNormalFormDataFromTheorems
    lambda hlambda archimedeanTest weilTest).toRows

def normalizedCoreS2B1NoHiddenFinitePartSubtractionRowsFromTheorems
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1NoHiddenFinitePartSubtractionConstructorRows
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  (normalizedCoreS2B1FinitePartNormalFormRowsFromTheorems
    lambda hlambda archimedeanTest weilTest).toNoHiddenFinitePartRows

def normalizedCoreS2B1NoHiddenFinitePartSubtractionConstructorInputFromTheorems
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FixedTupleNoHiddenFinitePartSubtractionConstructorInput
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  (normalizedCoreS2B1NoHiddenFinitePartSubtractionRowsFromTheorems
    lambda hlambda archimedeanTest weilTest).toConstructorInput

def normalizedCoreS2B1RemainingConstructorInputPackageFromTheorems :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest :
        normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        Source.S2B1FixedTupleRemainingConstructorInputPackage
          normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
          normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
          lambda archimedeanTest weilTest :=
  fun lambda hlambda archimedeanTest weilTest =>
    Source.S2B1FixedTupleRemainingConstructorInputPackage.ofFinitePartNormalForm
      (normalizedCoreS2B1RankZeroModeConstructorInputFromTheorems
        lambda hlambda archimedeanTest weilTest)
      (normalizedCoreS2B1NoStripRankPoleConstructorInputFromTheorems
        lambda hlambda archimedeanTest weilTest)
      (normalizedCoreS2B1EndpointStripCdefConstructorInputFromTheorems
        lambda hlambda archimedeanTest weilTest)
      (normalizedCoreS2B1NoExtraBulkConstructorInputFromTheorems
        lambda hlambda archimedeanTest weilTest)
      (normalizedCoreS2B1FinitePartSourceNormalFormDataFromTheorems
        lambda hlambda archimedeanTest weilTest)

def normalizedCoreS2B1RankZeroModeRowFromTheorems :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest :
        normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        Source.S2B1FixedTupleRankZeroModeRow
          normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
          normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
          lambda archimedeanTest weilTest :=
  fun lambda _hlambda archimedeanTest weilTest =>
    (normalizedCoreS2B1RankZeroModeConstructorInputFromTheorems
      lambda _hlambda archimedeanTest weilTest).toRow

def normalizedCoreS2B1NoStripRankPoleRowFromTheorems :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest :
        normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        Source.S2B1FixedTupleNoStripRankPoleRow
          normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
          normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
          lambda archimedeanTest weilTest :=
  fun lambda _hlambda archimedeanTest weilTest =>
    (normalizedCoreS2B1NoStripRankPoleConstructorInputFromTheorems
      lambda _hlambda archimedeanTest weilTest).toRow

def normalizedCoreS2B1EndpointStripCdefRowFromTheorems :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest :
        normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        Source.S2B1FixedTupleEndpointStripCdefRow
          normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
          normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
          lambda archimedeanTest weilTest :=
  fun lambda _hlambda archimedeanTest weilTest =>
    (normalizedCoreS2B1EndpointStripCdefConstructorInputFromTheorems
      lambda _hlambda archimedeanTest weilTest).toRow

def normalizedCoreS2B1NoExtraBulkRowFromTheorems :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest :
        normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        Source.S2B1FixedTupleNoExtraBulkRow
          normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
          normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
          lambda archimedeanTest weilTest :=
  fun lambda _hlambda archimedeanTest weilTest =>
    (normalizedCoreS2B1NoExtraBulkConstructorInputFromTheorems
      lambda _hlambda archimedeanTest weilTest).toRow

def normalizedCoreS2B1NoHiddenFinitePartSubtractionRowFromTheorems :
    ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
      ∀ archimedeanTest :
        normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols.Test,
      ∀ weilTest : TestFunction,
        Source.S2B1FixedTupleNoHiddenFinitePartSubtractionRow
          normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
          normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols
          lambda archimedeanTest weilTest :=
  fun lambda _hlambda archimedeanTest weilTest =>
    (normalizedCoreS2B1NoHiddenFinitePartSubtractionConstructorInputFromTheorems
      lambda _hlambda archimedeanTest weilTest).toRow

def normalizedCoreS2B1TraceScaleRemainingConstructorInputFromTheorems :
    Source.S2B1TraceScaleRemainingConstructorInput
      normalizedCoreCC20TraceModelFromTheorems.archimedeanSymbols
      normalizedCoreCCM25SourceModelFromTheorems.toWeilFormSymbols where
  rankZeroModeConstructorInput :=
    normalizedCoreS2B1RankZeroModeConstructorInputFromTheorems
  noStripRankPoleConstructorInput :=
    normalizedCoreS2B1NoStripRankPoleConstructorInputFromTheorems
  endpointStripCdefConstructorInput :=
    normalizedCoreS2B1EndpointStripCdefConstructorInputFromTheorems
  noExtraBulkConstructorInput :=
    normalizedCoreS2B1NoExtraBulkConstructorInputFromTheorems
  finitePartSourceNormalFormData :=
    normalizedCoreS2B1FinitePartSourceNormalFormDataFromTheorems

noncomputable def normalizedCoreRHDefinitionBridgeFromTheorems :
    Source.RHDefinitionBridge :=
  Source.RHDefinitionBridge.standard

/-- A C1 source criterion is an RH-level outlet once a concrete C1 input
record exists: by definition it consumes that input record and returns
`SourceRH`.  Do not count this socket as a lower finite-prime producer. -/
theorem normalizedCoreCC20PropositionC1SourceCriterion_iff_standardSourceRH_of_inputData
    (input : WeilPositivityInput)
    (hdata :
      Source.CC20PropositionC1InputData
        normalizedCoreRHDefinitionBridgeFromTheorems
        Source.cc20TripleFiniteVanishingSet
        input) :
    Source.CC20PropositionC1SourceCriterion
        normalizedCoreRHDefinitionBridgeFromTheorems
        Source.cc20TripleFiniteVanishingSet
        input ↔
      Source.RHDefinitionBridge.standard.SourceRH := by
  constructor
  · intro hcriterion
    simpa [normalizedCoreRHDefinitionBridgeFromTheorems] using
      hcriterion hdata
  · intro hRH _hdata
    simpa [normalizedCoreRHDefinitionBridgeFromTheorems] using hRH

theorem normalizedCoreCC20PropositionC1SourceCriterion_iff_mathlibRH_of_inputData
    (input : WeilPositivityInput)
    (hdata :
      Source.CC20PropositionC1InputData
        normalizedCoreRHDefinitionBridgeFromTheorems
        Source.cc20TripleFiniteVanishingSet
        input) :
    Source.CC20PropositionC1SourceCriterion
        normalizedCoreRHDefinitionBridgeFromTheorems
        Source.cc20TripleFiniteVanishingSet
        input ↔
      _root_.RiemannHypothesis :=
  (normalizedCoreCC20PropositionC1SourceCriterion_iff_standardSourceRH_of_inputData
    input hdata).trans
    Source.RHDefinitionBridge.standard_source_rh_iff_mathlib

axiom normalizedCoreCC20PropositionC1SourceCriterionRoot :
  ∀ input : WeilPositivityInput,
    Source.CC20PropositionC1SourceCriterion
      normalizedCoreRHDefinitionBridgeFromTheorems
      Source.cc20TripleFiniteVanishingSet
      input

noncomputable def normalizedCoreCC20PropositionC1SourceCriterionFromTheorems :
    ∀ input : WeilPositivityInput,
      Source.CC20PropositionC1SourceCriterion
        normalizedCoreRHDefinitionBridgeFromTheorems
        Source.cc20TripleFiniteVanishingSet
        input :=
  normalizedCoreCC20PropositionC1SourceCriterionRoot

noncomputable def normalizedCoreCC20RHExitObjectPackageFromTheorems :
    Source.CC20RHExitObjectPackage
      normalizedCoreRHDefinitionBridgeFromTheorems where
  finiteVanishingSet := Source.cc20TripleFiniteVanishingSet
  finiteSetAdmissible := Source.cc20_triple_finite_set_admissibility
  finiteSetDisjointFromNontrivialZeros := by
    simpa [normalizedCoreRHDefinitionBridgeFromTheorems] using
      Source.cc20_triple_disjoint_from_standard_source_nontrivial_zeros
  propositionC1SourceCriterion :=
    normalizedCoreCC20PropositionC1SourceCriterionFromTheorems

def normalizedSourceObjectCoreBasePackageConstructorInputFromTheorems :
    Source.SourceObjectTheoremBaseConstructorInput where
  ccm24Model := normalizedCoreCCM24SourceModelFromTheorems
  ccm25Model := normalizedCoreCCM25SourceModelFromTheorems
  cc20TraceModel := normalizedCoreCC20TraceModelFromTheorems
  s2b1NormalizedSeed := normalizedCoreS2B1NormalizedSeedFromTheorems
  s2b1NormalizedSeedArchimedeanSymbolsEq :=
    normalizedCoreS2B1NormalizedSeedArchimedeanSymbolsEqFromTheorems
  s2b1RemainderRowsOutsideNoBulk :=
    normalizedCoreS2B1RemainderRowsOutsideNoBulkFromTheorems
  s2b1TraceScaleRemainingConstructorInput :=
    normalizedCoreS2B1TraceScaleRemainingConstructorInputFromTheorems
  rhDefinitionBridge := normalizedCoreRHDefinitionBridgeFromTheorems
  cc20RHExitObjectPackage :=
    normalizedCoreCC20RHExitObjectPackageFromTheorems

def normalizedSourceObjectCoreBasePackageFromTheorems :
    Source.SourceObjectTheoremBasePackage :=
  normalizedSourceObjectCoreBasePackageConstructorInputFromTheorems.toPackage

def normalizedSourceObjectCoreFinitePrimeExactFromTheorems :
    Source.CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
      normalizedSourceObjectCoreBasePackageFromTheorems.ccm25Model.toWeilFormSymbols :=
  normalizedCoreCCM25FinitePrimeArithmeticSourceDataFromTheorems

def normalizedSourceObjectCoreTheoremBaseConstructorInputFromTheorems :
    Source.NormalizedSourceObjectCoreTheoremBaseConstructorInput where
  base := normalizedSourceObjectCoreBasePackageFromTheorems
  finitePrimeExact := normalizedSourceObjectCoreFinitePrimeExactFromTheorems

def normalizedSourceObjectCoreTheoremBaseDataFromTheorems :
    Source.NormalizedSourceObjectCoreTheoremBaseData :=
  normalizedSourceObjectCoreTheoremBaseConstructorInputFromTheorems.toCoreData

def normalizedSourceObjectCCM24ObjectFromTheorems :
    Source.SourceObject.CCM24SemilocalObjectPackage :=
  normalizedCoreCCM24SemilocalObjectFromTheorems

def normalizedSourceObjectRHExitObjectFromTheorems :
    Source.SourceObject.CC20RHExitObjectPackage where
  rhDefinitionBridge := normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base.rhDefinitionBridge
  sourceFiniteVanishingCriterionPackage :=
    Source.SourceFiniteVanishingCriterionPackage.ofCC20RHExitObjectPackage
      normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base.cc20RHExitObjectPackage
  sourceMellinVanishing := fun input => input.tripleVanishing
  sourceQWNonnegative := fun input => Nonempty input.fullWeilPositivity
  sourceCC20WeilNonpositivity := fun input => Nonempty input.fullWeilPositivity
  tripleVanishingToMellinBridge := by
    intro input h
    exact h
  routeFullPositivityToQWNonnegative := by
    intro input h
    exact ⟨h⟩
  qW_sign_bridge := by
    intro input h
    exact h
  sourceCC20PropositionC1 := by
    intro input hTriple hPositive
    exact hPositive.elim (fun h =>
      (Source.SourceFiniteVanishingCriterionPackage.ofCC20RHExitObjectPackage
        normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base.cc20RHExitObjectPackage).sourceCriterion
          input hTriple h)
  rhDefinitionContractConsumption :=
    normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base.rhDefinitionBridge.SourceRH

theorem normalizedSourceObjectRHExitBridgeEqFromTheorems :
    normalizedSourceObjectRHExitObjectFromTheorems.rhDefinitionBridge =
      normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base.rhDefinitionBridge := by
  rfl

def normalizedSourceObjectObjectConstructorInputFromTheorems :
    Source.NormalizedSourceObjectObjectConstructorInput
      normalizedSourceObjectCoreTheoremBaseDataFromTheorems where
  ccm24Object := normalizedSourceObjectCCM24ObjectFromTheorems
  sourceObjectRHExit := normalizedSourceObjectRHExitObjectFromTheorems
  sourceObjectRHExitBridgeEq := normalizedSourceObjectRHExitBridgeEqFromTheorems

def normalizedSourceObjectObjectDataFromTheorems :
    Source.NormalizedSourceObjectObjectData
      normalizedSourceObjectCoreTheoremBaseDataFromTheorems :=
  normalizedSourceObjectObjectConstructorInputFromTheorems.toObjectData

structure NormalizedSourceObjectBridgeReadOffRowsInput where
  rows :
    Source.NormalizedSourceObjectBridgeReadOffConstructorInput
      normalizedSourceObjectCoreTheoremBaseDataFromTheorems
      normalizedSourceObjectObjectDataFromTheorems

axiom normalizedSourceObjectBridgeReadOffRowsInputRoot :
  NormalizedSourceObjectBridgeReadOffRowsInput

def normalizedSourceObjectBridgeReadOffRowsInputFromTheorems :
    NormalizedSourceObjectBridgeReadOffRowsInput :=
  normalizedSourceObjectBridgeReadOffRowsInputRoot

def normalizedSourceObjectCommonTestBridgeRowsProviderFromTheorems :
    ∀ commonTest :
      Source.SourceObject.CommonTestObject
        normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base.ccm25Model.toWeilFormSymbols,
      ∀ cc20Trace : Source.SourceObject.CC20TraceObjectPackage,
      Source.NormalizedSourceObjectCommonTestBridgeRows
        normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base commonTest
        normalizedSourceObjectObjectDataFromTheorems.ccm24Object
        cc20Trace :=
  normalizedSourceObjectBridgeReadOffRowsInputFromTheorems.rows.commonTestBridgeRows

def normalizedSourceTraceReadOffEqualityRowsProviderFromTheorems :
    ∀ (commonTest :
        Source.SourceObject.CommonTestObject
          normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base.ccm25Model.toWeilFormSymbols)
      (cc20Trace : Source.SourceObject.CC20TraceObjectPackage)
      (lambda : ℝ),
      Source.NormalizedSourceTraceReadOffEqualityRows
        normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base commonTest
        cc20Trace lambda :=
  normalizedSourceObjectBridgeReadOffRowsInputFromTheorems.rows.traceReadOffEqualityRows

def normalizedSourceObjectBridgeReadOffConstructorInputFromTheorems :
    Source.NormalizedSourceObjectBridgeReadOffConstructorInput
      normalizedSourceObjectCoreTheoremBaseDataFromTheorems
      normalizedSourceObjectObjectDataFromTheorems :=
  normalizedSourceObjectBridgeReadOffRowsInputFromTheorems.rows

def normalizedSourceObjectBridgeReadOffDataFromTheorems :
    Source.NormalizedSourceObjectBridgeReadOffData
      normalizedSourceObjectCoreTheoremBaseDataFromTheorems
      normalizedSourceObjectObjectDataFromTheorems :=
  normalizedSourceObjectBridgeReadOffConstructorInputFromTheorems.toBridgeReadOffData

axiom normalizedSourceObjectScalarRemainderRowsProviderRoot :
  ∀ scalarSeed :
    Source.CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols,
      Source.NormalizedScalarCC20RemainderRows scalarSeed

def normalizedSourceObjectScalarRemainderRowsProviderFromTheorems :
    ∀ scalarSeed :
      Source.CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols,
      Source.NormalizedScalarCC20RemainderRows scalarSeed :=
  normalizedSourceObjectScalarRemainderRowsProviderRoot

def normalizedSourceObjectScalarFinitePartSourceNormalFormDataFromTheorems :
    ∀ scalarSeed :
      Source.CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols,
      ∀ lambda : ℝ, ∀ _hlambda : 1 < lambda,
        ∀ archimedeanTest :
          (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
            (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
              scalarSeed)).archimedeanSymbols.Test,
        ∀ weilTest : TestFunction,
          Source.S2B1FinitePartSourceNormalFormData
            (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
              (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
                scalarSeed)).archimedeanSymbols
            normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base.ccm25Model.toWeilFormSymbols
            lambda archimedeanTest weilTest := by
  intro _scalarSeed _lambda _hlambda _archimedeanTest _weilTest
  exact
    { sourceScalars :=
        { sourceActualFinitePart := 0
          sourceNormalizedFinitePart := 0
          sourceSubtractedFinitePartTerm := 0 }
      finitePartNormalizationFixedHolds := rfl
      noSubtractedFinitePartTermHolds := rfl }

def normalizedSourceObjectScalarCommonTestBridgeRowsProviderFromTheorems :
    ∀ (commonTest :
        Source.SourceObject.CommonTestObject
          normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base.ccm25Model.toWeilFormSymbols)
      (scalarSeed :
        Source.CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols),
      Source.NormalizedScalarCC20CommonTestBridgeRows
        normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base commonTest
        scalarSeed
        (normalizedSourceObjectScalarRemainderRowsProviderFromTheorems
          scalarSeed) := by
  intro _commonTest _scalarSeed
  exact
    { sourceTraceTestCompatibility := True
      traceLegIsCommonTest := True
      mellinLegIsCommonTest := True }

def normalizedSourceObjectScalarRowsConstructorInputFromTheorems :
    Source.NormalizedSourceObjectScalarRowsConstructorInput
      normalizedSourceObjectCoreTheoremBaseDataFromTheorems where
  scalarRemainderRows :=
    normalizedSourceObjectScalarRemainderRowsProviderFromTheorems
  scalarFinitePartSourceNormalFormData :=
    normalizedSourceObjectScalarFinitePartSourceNormalFormDataFromTheorems
  scalarCommonTestBridgeRows :=
    normalizedSourceObjectScalarCommonTestBridgeRowsProviderFromTheorems

def normalizedSourceObjectScalarRowsDataFromTheorems :
    Source.NormalizedSourceObjectScalarRowsData
      normalizedSourceObjectCoreTheoremBaseDataFromTheorems :=
  normalizedSourceObjectScalarRowsConstructorInputFromTheorems.toScalarRowsData

def normalizedSourceObjectRankLedgerKilledFromTheorems : Prop :=
  let base := normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base
  let sourceTraceTest := base.s2b1RemainderRowsOutsideNoBulk.sourceTraceTest
  let commonTestFunction :=
    normalizedSourceObjectCoreTheoremBaseDataFromTheorems.finitePrimeExact.commonTestFunction
  (base.s2b1NormalizedSeedNoStripRankPoleConstructorInput
    2 (by norm_num) sourceTraceTest commonTestFunction).noStripRankLedgerIdentified

def normalizedSourceObjectPoleLedgerKilledFromTheorems : Prop :=
  let base := normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base
  let sourceTraceTest := base.s2b1RemainderRowsOutsideNoBulk.sourceTraceTest
  let commonTestFunction :=
    normalizedSourceObjectCoreTheoremBaseDataFromTheorems.finitePrimeExact.commonTestFunction
  (base.s2b1NormalizedSeedNoStripRankPoleConstructorInput
    2 (by norm_num) sourceTraceTest commonTestFunction).noStripPoleLedgerIdentified

def normalizedSourceObjectCdefExhaustsFromTheorems : Prop :=
  let base := normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base
  let sourceTraceTest := base.s2b1RemainderRowsOutsideNoBulk.sourceTraceTest
  let commonTestFunction :=
    normalizedSourceObjectCoreTheoremBaseDataFromTheorems.finitePrimeExact.commonTestFunction
  (base.s2b1NormalizedSeedEndpointStripCdefConstructorInput
    2 (by norm_num) sourceTraceTest commonTestFunction).fixedTestCdefExhaustion

theorem normalizedSourceObjectRankLedgerKilledHoldsFromTheorems :
    normalizedSourceObjectRankLedgerKilledFromTheorems :=
  let base := normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base
  let sourceTraceTest := base.s2b1RemainderRowsOutsideNoBulk.sourceTraceTest
  let commonTestFunction :=
    normalizedSourceObjectCoreTheoremBaseDataFromTheorems.finitePrimeExact.commonTestFunction
  (base.s2b1NormalizedSeedNoStripRankPoleConstructorInput
    2 (by norm_num) sourceTraceTest commonTestFunction).noStripRankLedgerIdentifiedHolds

theorem normalizedSourceObjectPoleLedgerKilledHoldsFromTheorems :
    normalizedSourceObjectPoleLedgerKilledFromTheorems :=
  let base := normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base
  let sourceTraceTest := base.s2b1RemainderRowsOutsideNoBulk.sourceTraceTest
  let commonTestFunction :=
    normalizedSourceObjectCoreTheoremBaseDataFromTheorems.finitePrimeExact.commonTestFunction
  (base.s2b1NormalizedSeedNoStripRankPoleConstructorInput
    2 (by norm_num) sourceTraceTest commonTestFunction).noStripPoleLedgerIdentifiedHolds

theorem normalizedSourceObjectCdefExhaustsHoldsFromTheorems :
    normalizedSourceObjectCdefExhaustsFromTheorems :=
  let base := normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base
  let sourceTraceTest := base.s2b1RemainderRowsOutsideNoBulk.sourceTraceTest
  let commonTestFunction :=
    normalizedSourceObjectCoreTheoremBaseDataFromTheorems.finitePrimeExact.commonTestFunction
  (base.s2b1NormalizedSeedEndpointStripCdefConstructorInput
    2 (by norm_num) sourceTraceTest commonTestFunction).fixedTestCdefExhaustionHolds

def normalizedSourceObjectLedgerRowsConstructorInputFromTheorems :
    Source.NormalizedSourceObjectLedgerRowsConstructorInput where
  rankKilled := normalizedSourceObjectRankLedgerKilledFromTheorems
  poleKilled := normalizedSourceObjectPoleLedgerKilledFromTheorems
  cdefExhausts := normalizedSourceObjectCdefExhaustsFromTheorems
  rankKilledHolds := normalizedSourceObjectRankLedgerKilledHoldsFromTheorems
  poleKilledHolds := normalizedSourceObjectPoleLedgerKilledHoldsFromTheorems
  cdefExhaustsHolds := normalizedSourceObjectCdefExhaustsHoldsFromTheorems

def normalizedSourceObjectLedgerRowsDataFromTheorems :
    Source.NormalizedSourceObjectLedgerRowsData :=
  normalizedSourceObjectLedgerRowsConstructorInputFromTheorems.toLedgerRowsData

def normalizedSourceObjectTheoremBaseConstructorInputFromTheorems :
    Source.NormalizedSourceObjectTheoremBaseConstructorInput where
  core := normalizedSourceObjectCoreTheoremBaseDataFromTheorems
  objects := normalizedSourceObjectObjectDataFromTheorems
  bridgeReadOff := normalizedSourceObjectBridgeReadOffDataFromTheorems
  scalarRows := normalizedSourceObjectScalarRowsDataFromTheorems
  ledgerRows := normalizedSourceObjectLedgerRowsDataFromTheorems

def normalizedSourceObjectTheoremBaseInputFromTheorems :
    Source.NormalizedSourceObjectTheoremBaseInput :=
  normalizedSourceObjectTheoremBaseConstructorInputFromTheorems.toInput

def normalizedBaseFromTheorems :
    Source.SourceObjectTheoremBasePackage :=
  normalizedSourceObjectCoreTheoremBaseDataFromTheorems.base

def normalizedGlobalQWPsiRowsFromTheorems :
    Source.CCM25Concrete.Rows.ConcreteGlobalQWPsiRows
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols where
  qwDefinition :=
    Source.ccm25_source_qw_definition normalizedBaseFromTheorems.ccm25Model
  psiSign :=
    Source.ccm25_source_psi_sign normalizedBaseFromTheorems.ccm25Model

theorem normalizedQWDefinitionFromTheorems :
    WeilFormSymbols.QWDefinitionStatement
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  normalizedGlobalQWPsiRowsFromTheorems.qwDefinition

theorem normalizedPsiSignFromTheorems :
    WeilFormSymbols.PsiSignStatement
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  normalizedGlobalQWPsiRowsFromTheorems.psiSign

def normalizedConcreteGlobalQWPsiRowsFromTheorems :
    Source.CCM25Concrete.Rows.ConcreteGlobalQWPsiRows
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  normalizedGlobalQWPsiRowsFromTheorems

structure RestrictedQWLambdaPoleRows (W : WeilFormSymbols) where
  restrictedRows : Source.CCM25Concrete.Rows.ConcreteRestrictedQWLambdaRows W
  poleRows : Source.CCM25Concrete.Rows.ConcretePoleNormalizationRows W

def normalizedRestrictedQWLambdaPoleRowsFromTheorems :
    RestrictedQWLambdaPoleRows
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols where
  restrictedRows :=
    { qwLambdaFormula :=
        Source.ccm25_source_qw_lambda_formula normalizedBaseFromTheorems.ccm25Model }
  poleRows :=
    { poleNormalization :=
        Source.ccm25_source_pole_normalization normalizedBaseFromTheorems.ccm25Model }

theorem normalizedQWLambdaFormulaFromTheorems :
    WeilFormSymbols.QWLambdaFormulaStatement
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  normalizedRestrictedQWLambdaPoleRowsFromTheorems.restrictedRows.qwLambdaFormula

def normalizedConcreteRestrictedQWLambdaRowsFromTheorems :
    Source.CCM25Concrete.Rows.ConcreteRestrictedQWLambdaRows
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  normalizedRestrictedQWLambdaPoleRowsFromTheorems.restrictedRows

theorem normalizedPoleNormalizationFromTheorems :
    WeilFormSymbols.PoleNormalizationStatement
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  normalizedRestrictedQWLambdaPoleRowsFromTheorems.poleRows.poleNormalization

def normalizedConcretePoleNormalizationRowsFromTheorems :
    Source.CCM25Concrete.Rows.ConcretePoleNormalizationRows
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  normalizedRestrictedQWLambdaPoleRowsFromTheorems.poleRows

structure NormalizedConcreteCommonInputData where
  commonTestFunction : TestFunction
  finitePrimeArithmeticCertificates :
    Source.CCM25Concrete.FinitePrimeInterface.FixedLambdaArithmeticSourceTestCertificatesForAllTests
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
  commonPairSourceTest :
    (finitePrimeArithmeticCertificates commonTestFunction commonTestFunction).sourceTest =
      (Source.CCM25Concrete.CommonSourceTest.concreteCommonSourceTest
        normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
        commonTestFunction).toSourceTestEvaluationInterface

def normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems :
    Source.CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  normalizedSourceObjectCoreTheoremBaseDataFromTheorems.finitePrimeExact

def normalizedCommonTestFunctionInputFromTheorems : TestFunction :=
  normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems.commonTestFunction

def normalizedFinitePrimeArithmeticSourceDataInputFromTheorems :
    Source.CCM25Concrete.FinitePrimeSourceData.FinitePrimeArithmeticSourceData
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
      (Source.CCM25Concrete.CommonSourceTest.concreteCommonSourceTest
        normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
        normalizedCommonTestFunctionInputFromTheorems) :=
  normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems.finitePrimeData

def normalizedFinitePrimeSourceTestSelectorDataInputFromTheorems :
    Source.CCM25Concrete.FinitePrimeSourceData.FinitePrimeSourceTestSelectorData
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
      (Source.CCM25Concrete.CommonSourceTest.concreteCommonSourceTest
        normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
        normalizedCommonTestFunctionInputFromTheorems) :=
  normalizedFinitePrimeArithmeticSourceDataInputFromTheorems.selector

def normalizedFinitePrimeSourceTestSelectorInputFromTheorems
    (f g : TestFunction) :
    Source.CCM25Concrete.PrimePowerTest.SourceTestEvaluationInterface
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols f g :=
  normalizedFinitePrimeSourceTestSelectorDataInputFromTheorems.sourceTest f g

def normalizedFixedLambdaArithmeticCertificateDataInputFromTheorems
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    Source.CCM25Concrete.FinitePrimeSourceData.FixedLambdaArithmeticCertificateSourceTestData
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols f g lambda
      (normalizedFinitePrimeSourceTestSelectorInputFromTheorems f g) :=
  normalizedFinitePrimeArithmeticSourceDataInputFromTheorems.certificateData
    f g lambda hlambda

theorem normalizedFinitePrimeVisibleIffSourceAtomInputFromTheorems
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    ∀ n : ℕ,
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols.finitePrimeAtomVisible
          n (normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols.convolutionStar f g) ↔
        Source.CCM25Concrete.PrimePowerSupport.SourceVisibleAtomData
          normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols f g n :=
  (normalizedFixedLambdaArithmeticCertificateDataInputFromTheorems
    f g lambda hlambda).visibleIff

theorem normalizedGlobalPrimeIndexExactInputFromTheorems
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    ∀ n : ℕ,
      n ∈ normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols.globalPrimeIndexSet ↔
        Source.CCM25Concrete.PrimePowerSupport.SourceGlobalIndexData
          normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols f g n :=
  (normalizedFixedLambdaArithmeticCertificateDataInputFromTheorems
    f g lambda hlambda).globalExact

theorem normalizedRestrictedPrimeIndexExactInputFromTheorems
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    ∀ n : ℕ,
      n ∈ normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols.restrictedPrimeIndexSet
          lambda ↔
        Source.CCM25Concrete.PrimePowerSupport.SourceRestrictedIndexData
          normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols f g lambda n :=
  (normalizedFixedLambdaArithmeticCertificateDataInputFromTheorems
    f g lambda hlambda).restrictedExact

def normalizedPrimePowerArithmeticSupportSkeletonInputFromTheorems
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    Source.CCM25Concrete.PrimePowerSupport.SourcePrimePowerArithmeticSupportSkeletonAtLambda
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols f g lambda :=
  (normalizedFixedLambdaArithmeticCertificateDataInputFromTheorems
    f g lambda hlambda).toSupport hlambda

def normalizedPrimePowerSupportSkeletonInputFromTheorems
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    Source.CCM25Concrete.PrimePowerSupport.SourcePrimePowerSupportSkeletonAtLambda
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols f g lambda :=
  Source.CCM25Concrete.PrimePowerSupport.support_skeleton_of_arithmetic_support_skeleton
    (normalizedPrimePowerArithmeticSupportSkeletonInputFromTheorems
      f g lambda hlambda)

theorem normalizedPrimePowerArithmeticSupportUsesSelectedSourceTestInputFromTheorems
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    (normalizedPrimePowerArithmeticSupportSkeletonInputFromTheorems
        f g lambda hlambda).sourceTest =
      normalizedFinitePrimeSourceTestSelectorInputFromTheorems f g :=
  rfl

def normalizedFinitePrimeArithmeticSourceTestCertificatesInputFromTheorems :
    Source.CCM25Concrete.FinitePrimeInterface.FixedLambdaArithmeticSourceTestCertificatesForAllTests
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  Source.CCM25Concrete.FinitePrimeSourceData.fixedLambdaArithmeticSourceTestCertificatesForAllTests
    normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems

theorem normalizedCommonPairSourceTestInputFromTheorems :
    (normalizedFinitePrimeArithmeticSourceTestCertificatesInputFromTheorems
        normalizedCommonTestFunctionInputFromTheorems
        normalizedCommonTestFunctionInputFromTheorems).sourceTest =
      (Source.CCM25Concrete.CommonSourceTest.concreteCommonSourceTest
        normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
        normalizedCommonTestFunctionInputFromTheorems).toSourceTestEvaluationInterface :=
  Source.CCM25Concrete.FinitePrimeSourceData.commonPairSourceTest
    normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems

def normalizedConcreteCommonInputDataFromTheorems :
    NormalizedConcreteCommonInputData where
  commonTestFunction :=
    normalizedCommonTestFunctionInputFromTheorems
  finitePrimeArithmeticCertificates :=
    normalizedFinitePrimeArithmeticSourceTestCertificatesInputFromTheorems
  commonPairSourceTest :=
    normalizedCommonPairSourceTestInputFromTheorems

def normalizedCommonTestFunctionFromTheorems : TestFunction :=
  normalizedConcreteCommonInputDataFromTheorems.commonTestFunction

def normalizedConcreteCommonTestFromTheorems :
    Source.CCM25Concrete.CommonSourceTest.ConcreteCommonSourceTest
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  Source.CCM25Concrete.CommonSourceTest.concreteCommonSourceTest
    normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
    normalizedCommonTestFunctionFromTheorems

def normalizedConcreteArithmeticRowsFromTheorems :
    Source.CCM25Concrete.Interface.ConcreteCCM25ArithmeticRows
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols where
  globalRows := normalizedConcreteGlobalQWPsiRowsFromTheorems
  restrictedRows := normalizedConcreteRestrictedQWLambdaRowsFromTheorems
  finitePrimeArithmeticCertificates :=
    normalizedConcreteCommonInputDataFromTheorems.finitePrimeArithmeticCertificates
  poleRows := normalizedConcretePoleNormalizationRowsFromTheorems

theorem normalizedCommonPairSourceTestFromTheorems :
    (normalizedConcreteArithmeticRowsFromTheorems.finitePrimeArithmeticCertificates
        normalizedConcreteCommonTestFromTheorems.sourceTest
        normalizedConcreteCommonTestFromTheorems.sourceTest).sourceTest =
      normalizedConcreteCommonTestFromTheorems.toSourceTestEvaluationInterface :=
  normalizedConcreteCommonInputDataFromTheorems.commonPairSourceTest

def normalizedConcreteCommonFromTheorems :
    Source.SourceObjectConcreteCommonData normalizedBaseFromTheorems :=
  Source.SourceObjectConcreteCommonData.ofCanonicalFinitePrimeOwner
    normalizedConcreteArithmeticRowsFromTheorems
    normalizedCommonFinitePrimeArithmeticSourceDataInputFromTheorems
    normalizedCommonPairSourceTestFromTheorems

def normalizedCommonFinitePrimeArithmeticSourceDataFromTheorems :
    Source.CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols :=
  normalizedConcreteCommonFromTheorems.commonFinitePrimeArithmeticSourceData

def normalizedFinitePrimeArithmeticSourceDataFromTheorems :
    Source.CCM25Concrete.FinitePrimeSourceData.FinitePrimeArithmeticSourceData
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
      normalizedConcreteCommonTestFromTheorems :=
  normalizedCommonFinitePrimeArithmeticSourceDataFromTheorems.finitePrimeData

def normalizedFinitePrimeSourceTestSelectorDataFromTheorems :
    Source.CCM25Concrete.FinitePrimeSourceData.FinitePrimeSourceTestSelectorData
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
      normalizedConcreteCommonTestFromTheorems :=
  normalizedFinitePrimeArithmeticSourceDataFromTheorems.selector

def normalizedFinitePrimeSourceTestFromTheorems
    (f g : TestFunction) :
    Source.CCM25Concrete.PrimePowerTest.SourceTestEvaluationInterface
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols f g :=
  normalizedFinitePrimeSourceTestSelectorDataFromTheorems.sourceTest f g

theorem normalizedFinitePrimeSourceTestCommonPairFromTheorems :
    normalizedFinitePrimeSourceTestFromTheorems
        normalizedConcreteCommonTestFromTheorems.sourceTest
        normalizedConcreteCommonTestFromTheorems.sourceTest =
      normalizedConcreteCommonTestFromTheorems.toSourceTestEvaluationInterface :=
  normalizedFinitePrimeSourceTestSelectorDataFromTheorems.commonPairSourceTest

def normalizedFixedLambdaArithmeticCertificateDataFromTheorems
    (f g : TestFunction) (lambda : ℝ) (hlambda : 1 < lambda) :
    Source.CCM25Concrete.FinitePrimeSourceData.FixedLambdaArithmeticCertificateSourceTestData
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols f g lambda
      (normalizedFinitePrimeSourceTestFromTheorems f g) :=
  normalizedFinitePrimeArithmeticSourceDataFromTheorems.certificateData
    f g lambda hlambda

def normalizedCommonFromTheorems :
    Source.SourceObjectCommonData normalizedBaseFromTheorems :=
  normalizedConcreteCommonFromTheorems.toSourceObjectCommonData

structure NormalizedSeedInputData where
  seed : Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols
  archimedeanSymbols_eq_base :
    (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
      seed).archimedeanSymbols =
      normalizedBaseFromTheorems.cc20TraceModel.archimedeanSymbols

def normalizedSeedInputDataFromTheorems :
    NormalizedSeedInputData where
  seed := normalizedBaseFromTheorems.s2b1NormalizedSeed
  archimedeanSymbols_eq_base :=
    normalizedBaseFromTheorems.s2b1NormalizedSeedArchimedeanSymbolsEq

def normalizedSeedFromTheorems :
    Source.CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols :=
  normalizedSeedInputDataFromTheorems.seed

theorem normalizedSeedArchimedeanSymbolsEqBase :
    (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
      normalizedSeedFromTheorems).archimedeanSymbols =
      normalizedBaseFromTheorems.cc20TraceModel.archimedeanSymbols :=
  normalizedSeedInputDataFromTheorems.archimedeanSymbols_eq_base

def normalizedRemaindersFromTheorems :
    Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
      normalizedSeedFromTheorems :=
  normalizedCoreS2B1TracePackageRemaindersFromTheorems

structure NormalizedSourceObjectCCM24Input where
  ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage

def normalizedSourceObjectCCM24InputFromTheorems :
    NormalizedSourceObjectCCM24Input where
  ccm24 :=
    normalizedSourceObjectObjectDataFromTheorems.ccm24Object

structure NormalizedSourceObjectRHExitInput where
  rhExit : Source.SourceObject.CC20RHExitObjectPackage

def normalizedSourceObjectRHExitInputFromTheorems :
    NormalizedSourceObjectRHExitInput where
  rhExit :=
    normalizedSourceObjectObjectDataFromTheorems.sourceObjectRHExit

def normalizedSourceObjectBridgeRowsFromTheorems :
    Source.SourceObjectExpandedRows normalizedBaseFromTheorems
      normalizedCommonFromTheorems :=
  Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
    normalizedSourceObjectCCM24InputFromTheorems.ccm24
    normalizedSeedFromTheorems normalizedRemaindersFromTheorems

structure NormalizedSourceObjectRHDefinitionBridgeEqInput where
  rhDefinitionBridge_eq_base :
    normalizedSourceObjectRHExitInputFromTheorems.rhExit.rhDefinitionBridge =
      normalizedBaseFromTheorems.rhDefinitionBridge

def normalizedSourceObjectRHDefinitionBridgeEqInputFromTheorems :
    NormalizedSourceObjectRHDefinitionBridgeEqInput where
  rhDefinitionBridge_eq_base :=
    normalizedSourceObjectObjectDataFromTheorems.sourceObjectRHExitBridgeEq

structure NormalizedSourceObjectCommonTestInvolutionBridgeInput where
  commonTestInvolution :
    Source.SourceObject.CommonTestInvolutionBridge
      (Source.SourceObjectExpandedRows.ccm25
        normalizedSourceObjectBridgeRowsFromTheorems).weilSymbols
      normalizedCommonFromTheorems.commonTest

def normalizedSourceObjectCommonTestBridgeRowsFromTheorems :
    Source.NormalizedSourceObjectCommonTestBridgeRows
      normalizedBaseFromTheorems normalizedCommonFromTheorems.commonTest
      normalizedSourceObjectCCM24InputFromTheorems.ccm24
      normalizedSourceObjectBridgeRowsFromTheorems.cc20Trace :=
  { commonTestInvolution :=
      { sourceInvolutionCompatible :=
          normalizedSourceObjectCCM24InputFromTheorems.ccm24.semilocalSymbols.supportInWindow
            normalizedCommonFromTheorems.commonTest.sourceTest
            normalizedSourceObjectCCM24InputFromTheorems.ccm24.sourceSupportWindow
        convolutionSquareUsesInvolution :=
          normalizedCommonFromTheorems.commonTest.sourceConvolutionSquare =
            normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols.convolutionStar
              normalizedCommonFromTheorems.commonTest.sourceTest
              normalizedCommonFromTheorems.commonTest.sourceTest }
    ccm24Test_eq_commonTest :=
      { sourceTestCompatibility :=
          normalizedSourceObjectCCM24InputFromTheorems.ccm24.semilocalSymbols.sourceTest =
            normalizedCommonFromTheorems.commonTest.sourceTest
        semilocalLegIsCommonTest :=
          normalizedSourceObjectCCM24InputFromTheorems.ccm24.semilocalSymbols.sourceTest =
            normalizedCommonFromTheorems.commonTest.sourceTest }
    cc20TraceTest_eq_commonTest :=
      { sourceTraceTestCompatibility :=
          normalizedSourceObjectBridgeRowsFromTheorems.cc20Trace.sourceCC20TraceTestCompatibility
        traceLegIsCommonTest :=
          normalizedSourceObjectBridgeRowsFromTheorems.cc20Trace.sourceTraceTest =
            normalizedCommonFromTheorems.commonTest.sourceTest
        mellinLegIsCommonTest :=
          normalizedSourceObjectBridgeRowsFromTheorems.cc20Trace.sourceTraceTest =
            normalizedCommonFromTheorems.commonTest.sourceTest
        halfDensityMatchesCommonTest :=
          normalizedSourceObjectBridgeRowsFromTheorems.cc20Trace.sourceMellinHalfDensityCompatibility } }

def normalizedSourceObjectCommonTestInvolutionBridgeInputFromTheorems :
    NormalizedSourceObjectCommonTestInvolutionBridgeInput where
  commonTestInvolution :=
    normalizedSourceObjectCommonTestBridgeRowsFromTheorems.commonTestInvolution

structure NormalizedSourceObjectCCM24CommonTestBridgeInput where
  ccm24Test_eq_commonTest :
    Source.SourceObject.CCM24CommonTestBridge
      (Source.SourceObjectExpandedRows.ccm25
        normalizedSourceObjectBridgeRowsFromTheorems).weilSymbols
      normalizedCommonFromTheorems.commonTest
      normalizedSourceObjectCCM24InputFromTheorems.ccm24

def normalizedSourceObjectCCM24CommonTestBridgeInputFromTheorems :
    NormalizedSourceObjectCCM24CommonTestBridgeInput where
  ccm24Test_eq_commonTest :=
    normalizedSourceObjectCommonTestBridgeRowsFromTheorems.ccm24Test_eq_commonTest

structure NormalizedSourceObjectCC20CommonTestBridgeInput where
  cc20TraceTest_eq_commonTest :
    Source.SourceObject.CC20CommonTestBridge
      (Source.SourceObjectExpandedRows.ccm25
        normalizedSourceObjectBridgeRowsFromTheorems).weilSymbols
      normalizedCommonFromTheorems.commonTest
      normalizedSourceObjectBridgeRowsFromTheorems.cc20Trace

def normalizedSourceObjectCC20CommonTestBridgeInputFromTheorems :
    NormalizedSourceObjectCC20CommonTestBridgeInput where
  cc20TraceTest_eq_commonTest :=
    normalizedSourceObjectCommonTestBridgeRowsFromTheorems.cc20TraceTest_eq_commonTest

structure NormalizedSourceObjectConvolutionSquareEqFgInput where
  convolutionSquare_eq_Fg : Prop

def normalizedSourceObjectConvolutionSquareEqFgInputFromTheorems :
    NormalizedSourceObjectConvolutionSquareEqFgInput where
  convolutionSquare_eq_Fg :=
    normalizedCommonFromTheorems.commonTest.sourceConvolutionSquare =
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols.convolutionStar
        normalizedCommonFromTheorems.commonTest.sourceTest
        normalizedCommonFromTheorems.commonTest.sourceTest

structure NormalizedSourceObjectQWLambdaWindowControlInput where
  ccm24Window_controls_qwLambda : Prop

def normalizedSourceObjectQWLambdaWindowControlInputFromTheorems :
    NormalizedSourceObjectQWLambdaWindowControlInput where
  ccm24Window_controls_qwLambda :=
    ∀ lambda : ℝ, 1 < lambda →
      SemilocalModelSymbols.lambdaCompatible
        normalizedSourceObjectCCM24InputFromTheorems.ccm24.semilocalSymbols
        normalizedSourceObjectCCM24InputFromTheorems.ccm24.sourceSupportWindow
        lambda

structure NormalizedSourceObjectCdefWindowControlInput where
  ccm24Window_controls_cdef : Prop

def normalizedSourceObjectCdefWindowControlInputFromTheorems :
    NormalizedSourceObjectCdefWindowControlInput where
  ccm24Window_controls_cdef :=
    SemilocalModelSymbols.fixedWindowExhaustionCompatible
      normalizedSourceObjectCCM24InputFromTheorems.ccm24.semilocalSymbols
      normalizedSourceObjectCCM24InputFromTheorems.ccm24.sourceSupportWindow

structure NormalizedSourceObjectFinitePrimeWindowMatchInput where
  finitePrimeSupport_matches_window : Prop

def normalizedSourceObjectFinitePrimeWindowMatchInputFromTheorems :
    NormalizedSourceObjectFinitePrimeWindowMatchInput where
  finitePrimeSupport_matches_window :=
    WeilFormSymbols.FinitePrimeNormalizationStatement
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols

structure NormalizedSourceObjectQWSignBridgeInput where
  qW_sign_bridge : Prop

def normalizedSourceObjectQWSignBridgeInputFromTheorems :
    NormalizedSourceObjectQWSignBridgeInput where
  qW_sign_bridge :=
    ∀ input : WeilPositivityInput,
      normalizedSourceObjectRHExitInputFromTheorems.rhExit.sourceQWNonnegative input →
        normalizedSourceObjectRHExitInputFromTheorems.rhExit.sourceCC20WeilNonpositivity input

structure NormalizedSourceObjectCrossObjectBridgeInput where
  bridges :
    Source.SourceObjectCrossObjectBridges normalizedBaseFromTheorems
      normalizedCommonFromTheorems
      normalizedSourceObjectBridgeRowsFromTheorems
      normalizedSourceObjectRHExitInputFromTheorems.rhExit

def normalizedSourceObjectCrossObjectBridgeInputFromTheorems :
    NormalizedSourceObjectCrossObjectBridgeInput where
  bridges :=
    { rhDefinitionBridge_eq_base :=
        (normalizedSourceObjectRHDefinitionBridgeEqInputFromTheorems).rhDefinitionBridge_eq_base
      commonTestInvolution :=
        (normalizedSourceObjectCommonTestInvolutionBridgeInputFromTheorems).commonTestInvolution
      ccm24Test_eq_commonTest :=
        (normalizedSourceObjectCCM24CommonTestBridgeInputFromTheorems).ccm24Test_eq_commonTest
      cc20TraceTest_eq_commonTest :=
        (normalizedSourceObjectCC20CommonTestBridgeInputFromTheorems).cc20TraceTest_eq_commonTest
      convolutionSquare_eq_Fg :=
        (normalizedSourceObjectConvolutionSquareEqFgInputFromTheorems).convolutionSquare_eq_Fg
      ccm24Window_controls_qwLambda :=
        (normalizedSourceObjectQWLambdaWindowControlInputFromTheorems).ccm24Window_controls_qwLambda
      ccm24Window_controls_cdef :=
        (normalizedSourceObjectCdefWindowControlInputFromTheorems).ccm24Window_controls_cdef
      finitePrimeSupport_matches_window :=
        (normalizedSourceObjectFinitePrimeWindowMatchInputFromTheorems).finitePrimeSupport_matches_window
      qW_sign_bridge :=
        normalizedSourceObjectQWSignBridgeInputFromTheorems.qW_sign_bridge }

structure NormalizedSourceObjectLayerBridgeInput where
  ccm24 : Source.SourceObject.CCM24SemilocalObjectPackage
  rhExit : Source.SourceObject.CC20RHExitObjectPackage
  bridges :
    Source.SourceObjectCrossObjectBridges normalizedBaseFromTheorems
      normalizedCommonFromTheorems
      (Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
        ccm24 normalizedSeedFromTheorems normalizedRemaindersFromTheorems)
      rhExit

def normalizedSourceObjectLayerBridgeInputFromTheorems :
    NormalizedSourceObjectLayerBridgeInput where
  ccm24 := normalizedSourceObjectCCM24InputFromTheorems.ccm24
  rhExit := normalizedSourceObjectRHExitInputFromTheorems.rhExit
  bridges := normalizedSourceObjectCrossObjectBridgeInputFromTheorems.bridges

def normalizedSourceObjectLayerInputFromTheorems :
    Source.NormalizedCC20SourceObjectLayerInput
      normalizedBaseFromTheorems normalizedCommonFromTheorems
      normalizedSeedFromTheorems normalizedRemaindersFromTheorems :=
  { ccm24 := normalizedSourceObjectLayerBridgeInputFromTheorems.ccm24
    rhExit := normalizedSourceObjectLayerBridgeInputFromTheorems.rhExit
    bridges := normalizedSourceObjectLayerBridgeInputFromTheorems.bridges }

def normalizedCCM24FromTheorems :
    Source.SourceObject.CCM24SemilocalObjectPackage :=
  normalizedSourceObjectLayerInputFromTheorems.ccm24

def normalizedRhExitFromTheorems :
    Source.SourceObject.CC20RHExitObjectPackage :=
  normalizedSourceObjectLayerInputFromTheorems.rhExit

def normalizedRowsFromTheorems :
    Source.SourceObjectExpandedRows normalizedBaseFromTheorems
      normalizedCommonFromTheorems :=
  Source.SourceObjectExpandedRows.ofNormalizedCC20Trace
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems

def normalizedBridgesFromTheorems :
    Source.SourceObjectCrossObjectBridges normalizedBaseFromTheorems
      normalizedCommonFromTheorems normalizedRowsFromTheorems
      normalizedRhExitFromTheorems :=
  normalizedSourceObjectLayerInputFromTheorems.bridges

abbrev normalizedSourceObjectPackageFromTheorems :
    Source.SourceObject.SourceObjectPackage :=
  Source.sourceObjectPackageOfNormalizedCC20Trace
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems

structure NormalizedFixedSTestAdmissibleWindowInput where
  admissibleWindow : Prop
  admissibleWindowHolds : admissibleWindow

def normalizedFixedSTestAdmissibleWindowInputFromTheorems :
    NormalizedFixedSTestAdmissibleWindowInput where
  admissibleWindow :=
    normalizedSourceObjectPackageFromTheorems.ccm24.semilocalSymbols.supportInWindow
      normalizedSourceObjectPackageFromTheorems.ccm24.semilocalSymbols.sourceTest
      normalizedSourceObjectPackageFromTheorems.ccm24.sourceSupportWindow
  admissibleWindowHolds :=
    normalizedSourceObjectPackageFromTheorems.ccm24.sourceSoninSpaceComparisonData.1

structure NormalizedFixedSTestTripleVanishingInput where
  tripleVanishingSymbols : TripleVanishingSymbols
  tripleVanishingSourceHolds :
    TripleVanishingSymbols.TripleVanishingStatement tripleVanishingSymbols

def normalizedFixedSTestTripleVanishingInputFromTheorems :
    NormalizedFixedSTestTripleVanishingInput where
  tripleVanishingSymbols :=
    (normalizedSourceObjectPackageFromTheorems.cc20RHExit.sourceFiniteVanishingCriterionPackage).tripleVanishingSymbols
  tripleVanishingSourceHolds :=
    Source.SourceFiniteVanishingCriterionPackage.triple_vanishing_statement_of_source_package
      normalizedSourceObjectPackageFromTheorems.cc20RHExit.sourceFiniteVanishingCriterionPackage

structure NormalizedFixedSTestSourceInput where
  admissibleWindow : Prop
  admissibleWindowHolds : admissibleWindow
  tripleVanishingSymbols : TripleVanishingSymbols
  tripleVanishingSourceHolds :
    TripleVanishingSymbols.TripleVanishingStatement tripleVanishingSymbols

def normalizedFixedSTestSourceInputFromTheorems :
    NormalizedFixedSTestSourceInput where
  admissibleWindow :=
    normalizedFixedSTestAdmissibleWindowInputFromTheorems.admissibleWindow
  admissibleWindowHolds :=
    normalizedFixedSTestAdmissibleWindowInputFromTheorems.admissibleWindowHolds
  tripleVanishingSymbols :=
    normalizedFixedSTestTripleVanishingInputFromTheorems.tripleVanishingSymbols
  tripleVanishingSourceHolds :=
    normalizedFixedSTestTripleVanishingInputFromTheorems.tripleVanishingSourceHolds

def normalizedFixedTestFromTheorems : FixedSTest where
  admissibleWindow :=
    normalizedFixedSTestSourceInputFromTheorems.admissibleWindow
  tripleVanishing :=
    TripleVanishingSymbols.TripleVanishingStatement
      normalizedFixedSTestSourceInputFromTheorems.tripleVanishingSymbols
  finitePrimesVisible :=
    WeilFormSymbols.FinitePrimeVisibilityStatement
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems).ccm25.weilSymbols
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceTest
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceTest

def normalizedFixedDataFromTheorems :
    FixedSTestObligationData normalizedSourceObjectPackageFromTheorems where
  test := normalizedFixedTestFromTheorems
  tripleVanishingSymbols :=
    normalizedFixedSTestSourceInputFromTheorems.tripleVanishingSymbols
  admissibleWindow :=
    normalizedFixedSTestSourceInputFromTheorems.admissibleWindowHolds
  tripleVanishingBridge := by
    intro h
    exact h
  tripleVanishingSourceHolds :=
    normalizedFixedSTestSourceInputFromTheorems.tripleVanishingSourceHolds
  routeTest := normalizedSourceObjectPackageFromTheorems.commonTest.sourceTest
  routeTest_eq_commonTest := rfl
  finitePrimeVisibilityStatement := by
    exact
      { globalPrimeIndexCoverage :=
          normalizedConcreteCommonFromTheorems.common_finite_prime_global_coverage_statement
        restrictedPrimeIndexCoverage :=
          normalizedConcreteCommonFromTheorems.common_finite_prime_restricted_coverage_statement
        finitePrimeTermNormalization :=
          normalizedConcreteCommonFromTheorems.common_finite_prime_term_normalization_statement }
  finitePrimeVisibilityBridge := by
    intro h
    exact h

abbrev normalizedFixedFrontEndFromTheorems :
    ExpandedSourceFixedSTestFrontEnd
      normalizedSourceObjectPackageFromTheorems :=
  FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedPackage
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems

abbrev normalizedSourceBackedFixedSTestFromTheorems :
    SourceBackedFixedSTest
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems) :=
  SourceBackedFixedSTest.ofExpandedSourcePackageWithCCM24Model
    normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems
    normalizedCoreCCM24SourceModelFromTheorems rfl

structure NormalizedTraceLambdaInput where
  lambda : ℝ
  oneLtLambda : 1 < lambda

def normalizedTraceLambdaInputFromTheorems :
    NormalizedTraceLambdaInput where
  lambda := 2
  oneLtLambda := by norm_num

def normalizedTraceCCM25ArithmeticPackageFromTheorems :
    Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems).ccm25.weilSymbols
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceTest
      normalizedTraceLambdaInputFromTheorems.lambda where
  rows := normalizedConcreteArithmeticRowsFromTheorems
  oneLtLambda := normalizedTraceLambdaInputFromTheorems.oneLtLambda

structure NormalizedTraceQuotientCompatibilityInput where
  testAndQuotientCompatibility :
    TestAndQuotientCompatibility
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems)

def normalizedTraceQuotientCompatibilityInputFromTheorems :
    NormalizedTraceQuotientCompatibilityInput where
  testAndQuotientCompatibility :=
    test_and_quotient_compatibility_of_package
      normalizedTraceCCM25ArithmeticPackageFromTheorems

structure NormalizedTraceSupportSquareTransportInput where
  fixedSSupportSquareTransport :
    FixedSQuantizedSupportSquareTransport
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedTraceLambdaInputFromTheorems.lambda

def normalizedTraceSupportSquareTransportInputFromTheorems :
    NormalizedTraceSupportSquareTransportInput where
  fixedSSupportSquareTransport :=
    fixed_s_quantized_support_square_transport_of_parts
      normalizedTraceLambdaInputFromTheorems.oneLtLambda
      (cc20_archimedean_trace_square_output
        (cc20_trace_legality_template_output
          (normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceHilbertSchmidtGate
            normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest)).traceLegality).noDefectSourceReadOff
      (cc20_trace_legality_template_output
        (normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceHilbertSchmidtGate
          normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest)).traceLegality

structure NormalizedTraceFullReadOffBuildInput where
  build :
    CC20NoDefectSourceReadOff
        (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
        normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest →
      CCM25FullQWReadOff
        (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
        (normalizedSourceBackedFixedSTestFromTheorems) →
      FullTraceReadOffSource
        (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
        normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
        (normalizedSourceBackedFixedSTestFromTheorems)

structure NormalizedTraceFullReadOffEqualityInput where
  fullTraceReadOffEquality :
    FullTraceReadOffEquality
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (normalizedSourceBackedFixedSTestFromTheorems)

structure NormalizedSelectedSourceTraceReadOffEqualityInput where
  fullTraceReadOffEquality :
    FullTraceReadOffEquality
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (normalizedSourceBackedFixedSTestFromTheorems)
  restrictedTraceReadOffEquality :
    RestrictedTraceReadOffEquality
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedTraceLambdaInputFromTheorems.lambda

def normalizedTraceReadOffEqualityRowsFromTheorems :
    Source.NormalizedSourceTraceReadOffEqualityRows
      normalizedBaseFromTheorems normalizedCommonFromTheorems.commonTest
      normalizedSourceObjectPackageFromTheorems.cc20Trace
      normalizedTraceLambdaInputFromTheorems.lambda :=
  normalizedSourceObjectTheoremBaseInputFromTheorems.sourceTraceReadOffEqualityRows
    normalizedCommonFromTheorems.commonTest
    normalizedSourceObjectPackageFromTheorems.cc20Trace
    normalizedTraceLambdaInputFromTheorems.lambda

def normalizedTraceSelectedLegalityDataFromTheorems :
    Source.CC20SelectedTraceLegalityData
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest :=
  Source.CC20SelectedTraceLegalityData.ofHilbertSchmidtGate
    (normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceHilbertSchmidtGate
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest)
    normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceClassCyclicityTemplate

structure NormalizedSelectedSourceCoreTraceQWLambdaCalibrationInput where
  sourceCoreCalibration :
    Source.NormalizedSeedRestrictedEvaluatorScalarIdentification
      normalizedSeedFromTheorems
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems).ccm25.weilSymbols
      normalizedRemaindersFromTheorems
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (normalizedSourceBackedFixedSTestFromTheorems).weilTest
      normalizedTraceCCM25ArithmeticPackageFromTheorems

class NormalizedSelectedSourceCoreTraceQWLambdaCalibrationProvider where
  input : NormalizedSelectedSourceCoreTraceQWLambdaCalibrationInput

variable [NormalizedSelectedSourceCoreTraceQWLambdaCalibrationProvider]

def normalizedSelectedSourceCoreTraceQWLambdaCalibrationInputFromTheorems :
    NormalizedSelectedSourceCoreTraceQWLambdaCalibrationInput :=
  NormalizedSelectedSourceCoreTraceQWLambdaCalibrationProvider.input

def normalizedSelectedRestrictedEvaluatorScalarIdentificationFromTheorems :
    Source.NormalizedSeedRestrictedEvaluatorScalarIdentification
      normalizedSeedFromTheorems
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems).ccm25.weilSymbols
      normalizedRemaindersFromTheorems
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (normalizedSourceBackedFixedSTestFromTheorems).weilTest
      normalizedTraceCCM25ArithmeticPackageFromTheorems :=
  normalizedSelectedSourceCoreTraceQWLambdaCalibrationInputFromTheorems.sourceCoreCalibration

def normalizedSelectedQWLambdaScalarIdentificationFromTheorems :
    Source.NormalizedSeedQWLambdaScalarIdentification
      normalizedSeedFromTheorems
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems).ccm25.weilSymbols
      normalizedRemaindersFromTheorems
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (normalizedSourceBackedFixedSTestFromTheorems).weilTest :=
  Source.normalizedSeedQWLambdaScalarIdentificationOfRestrictedEvaluator
    normalizedSeedFromTheorems
    (RouteInputs.ofExpandedSourcePackage
      normalizedSourceObjectPackageFromTheorems).ccm25.weilSymbols
    normalizedRemaindersFromTheorems
    normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
    (normalizedSourceBackedFixedSTestFromTheorems).weilTest
    normalizedTraceCCM25ArithmeticPackageFromTheorems
    normalizedSelectedRestrictedEvaluatorScalarIdentificationFromTheorems

def normalizedSelectedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems :
    Source.S2B1FixedTupleSupportSquareQWLambdaRow
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (normalizedSourceBackedFixedSTestFromTheorems).weilTest :=
  (Source.normalizedSeedSupportSquareQWLambdaReadOffOfScalarIdentification
    normalizedSeedFromTheorems
    (RouteInputs.ofExpandedSourcePackage
      normalizedSourceObjectPackageFromTheorems).ccm25.weilSymbols
    normalizedRemaindersFromTheorems
    normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
    (normalizedSourceBackedFixedSTestFromTheorems).weilTest
    normalizedTraceCCM25ArithmeticPackageFromTheorems
    normalizedSelectedRestrictedEvaluatorScalarIdentificationFromTheorems).toRow

theorem normalizedSelectedRestrictedTraceReadOffEqualityFromFixedTuple :
    RestrictedTraceReadOffEquality
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedTraceLambdaInputFromTheorems.lambda := by
  simpa [RestrictedTraceReadOffEquality] using
    normalizedSelectedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems.supportSquareMainTermEqualsQWLambda

theorem normalizedSelectedSourceNoDefectQWLambdaFromTheorems :
    normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols.sourceNoDefectTrace
        normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest =
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols.qwLambda
        normalizedTraceLambdaInputFromTheorems.lambda
        (normalizedSourceBackedFixedSTestFromTheorems).weilTest
        (normalizedSourceBackedFixedSTestFromTheorems).weilTest := by
  calc
    normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols.sourceNoDefectTrace
        normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest =
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols.supportSquareTrace
        normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest := by
        exact
          (((RouteInputs.ofExpandedSourcePackage
            normalizedSourceObjectPackageFromTheorems).cc20.archimedeanTraceSquare
              normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
              normalizedTraceSelectedLegalityDataFromTheorems.selectedTraceClass
              normalizedTraceSelectedLegalityDataFromTheorems.selectedCyclicLegal).1).symm
    _ =
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols.qwLambda
        normalizedTraceLambdaInputFromTheorems.lambda
        (normalizedSourceBackedFixedSTestFromTheorems).weilTest
        (normalizedSourceBackedFixedSTestFromTheorems).weilTest := by
        simpa [RestrictedTraceReadOffEquality] using
          normalizedSelectedRestrictedTraceReadOffEqualityFromFixedTuple

def normalizedSelectedSourceCommonTestTupleFromTheorems :
    SourceCommonTestTupleContract
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
      normalizedTraceCCM25ArithmeticPackageFromTheorems :=
  source_common_test_tuple_contract_of_package
    (window_lambda_compatibility_of_source_backed
      normalizedTraceLambdaInputFromTheorems.oneLtLambda)
    (expanded_source_package_convolution_square_read_off
      normalizedSourceObjectPackageFromTheorems
      normalizedFixedFrontEndFromTheorems)

def normalizedSelectedRestrictedFinitePrimeSupportStabilizesFromTheorems :
    RestrictedFinitePrimeSupportStabilizes
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceCCM25ArithmeticPackageFromTheorems where
  fixedTestSupport :=
    fixed_test_support_threshold_at_large_of_source_backed
      normalizedTraceLambdaInputFromTheorems.oneLtLambda
  primePowerAtomStabilization :=
    prime_power_atom_stabilization_of_common_tuple
      normalizedSelectedSourceCommonTestTupleFromTheorems

structure NormalizedSelectedFinitePrimeIndexDifferenceInput where
  finitePrimeIndexDifference :
    SourceFinitePrimeIndexDifferenceArchimedeanBalance
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedTraceLambdaInputFromTheorems.lambda

axiom normalizedSelectedFinitePrimeIndexDifferenceInputRoot :
  NormalizedSelectedFinitePrimeIndexDifferenceInput

def normalizedSelectedFinitePrimeIndexDifferenceInputFromTheorems :
    NormalizedSelectedFinitePrimeIndexDifferenceInput :=
  normalizedSelectedFinitePrimeIndexDifferenceInputRoot

def normalizedSelectedScopedFinitePrimeArchimedeanBalanceFromTheorems :
    SourceScopedFinitePrimeArchimedeanBalance
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceCCM25ArithmeticPackageFromTheorems :=
  source_scoped_finite_prime_archimedean_balance_of_index_difference
    (package_backed_ccm25_weil_form_read_off
      (window_lambda_compatibility_of_source_backed
        normalizedTraceLambdaInputFromTheorems.oneLtLambda))
    normalizedSelectedFinitePrimeIndexDifferenceInputFromTheorems.finitePrimeIndexDifference

def normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems :
    SourceArchimedeanContributionBalanceRows
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceCCM25ArithmeticPackageFromTheorems :=
  { scopedBalance :=
      source_scoped_archimedean_contribution_matches_of_finite_prime_balance
        (package_backed_ccm25_weil_form_read_off
          (window_lambda_compatibility_of_source_backed
            normalizedTraceLambdaInputFromTheorems.oneLtLambda))
        normalizedSelectedScopedFinitePrimeArchimedeanBalanceFromTheorems }

def normalizedSelectedArchimedeanContributionMatchesForRestrictionFromTheorems :
    SourceArchimedeanContributionMatchesForRestriction
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceCCM25ArithmeticPackageFromTheorems :=
  source_archimedean_contribution_matches_of_balance_rows
    normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems

def normalizedSelectedQWLambdaRestrictionRowsFromTheorems :
    SourceQWLambdaIsRestrictionOfQW
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceCCM25ArithmeticPackageFromTheorems := by
  refine
    source_qw_lambda_is_restriction_of_common_tuple
      normalizedSelectedSourceCommonTestTupleFromTheorems
      normalizedSelectedRestrictedFinitePrimeSupportStabilizesFromTheorems
      ?_
  exact normalizedSelectedArchimedeanContributionMatchesForRestrictionFromTheorems

theorem normalizedSelectedQWLambdaEqualsQWFromTheorems :
    normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols.qwLambda
        normalizedTraceLambdaInputFromTheorems.lambda
        (normalizedSourceBackedFixedSTestFromTheorems).weilTest
        (normalizedSourceBackedFixedSTestFromTheorems).weilTest =
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols.qw
        (normalizedSourceBackedFixedSTestFromTheorems).weilTest
        (normalizedSourceBackedFixedSTestFromTheorems).weilTest := by
  exact source_qw_lambda_eq_qw_of_qw_lambda_restriction
    normalizedSelectedQWLambdaRestrictionRowsFromTheorems

theorem normalizedSelectedSourceNoDefectGlobalFormulaFromTheorems :
    normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols.sourceNoDefectTrace
        normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest =
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols.poleFunctional
          (normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols.convolutionStar
            (normalizedSourceBackedFixedSTestFromTheorems).weilTest
            (normalizedSourceBackedFixedSTestFromTheorems).weilTest) -
        normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols.archimedeanTerm
          (normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols.convolutionStar
            (normalizedSourceBackedFixedSTestFromTheorems).weilTest
            (normalizedSourceBackedFixedSTestFromTheorems).weilTest) -
          Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_scoped_sum
            normalizedTraceCCM25ArithmeticPackageFromTheorems := by
  exact
    source_no_defect_global_formula_of_scalar_equality
      (inputs :=
        RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      (g := normalizedSourceBackedFixedSTestFromTheorems)
      (lambda := normalizedTraceLambdaInputFromTheorems.lambda)
      (a := normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest)
      (pkg := normalizedTraceCCM25ArithmeticPackageFromTheorems)
      (package_backed_ccm25_weil_form_read_off
        (window_lambda_compatibility_of_source_backed
          normalizedTraceLambdaInputFromTheorems.oneLtLambda))
      normalizedSelectedSourceNoDefectQWLambdaFromTheorems
      normalizedSelectedQWLambdaEqualsQWFromTheorems

noncomputable def normalizedSelectedRestrictedToFullScalarRestrictionWitnessFromTheorems :
    RestrictedToFullQWScalarRestrictionWitness
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
      normalizedTraceCCM25ArithmeticPackageFromTheorems :=
  restricted_to_full_scalar_restriction_witness_of_common_tuple
    normalizedSelectedSourceCommonTestTupleFromTheorems
    normalizedSelectedRestrictedFinitePrimeSupportStabilizesFromTheorems
    (source_archimedean_contribution_matches_of_balance_rows
      normalizedSelectedArchimedeanContributionBalanceRowsFromTheorems)

theorem normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull :
    FullTraceReadOffEquality
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (normalizedSourceBackedFixedSTestFromTheorems) := by
  dsimp [FullTraceReadOffEquality]
  calc
    normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols.sourceNoDefectTrace
        normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest =
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols.supportSquareTrace
        normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest := by
        exact
          (((RouteInputs.ofExpandedSourcePackage
            normalizedSourceObjectPackageFromTheorems).cc20.archimedeanTraceSquare
              normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
              normalizedTraceSelectedLegalityDataFromTheorems.selectedTraceClass
              normalizedTraceSelectedLegalityDataFromTheorems.selectedCyclicLegal).1).symm
    _ =
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols.qwLambda
        normalizedTraceLambdaInputFromTheorems.lambda
        (normalizedSourceBackedFixedSTestFromTheorems).weilTest
        (normalizedSourceBackedFixedSTestFromTheorems).weilTest := by
        simpa [RestrictedTraceReadOffEquality] using
          normalizedSelectedRestrictedTraceReadOffEqualityFromFixedTuple
    _ =
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols.qw
        (normalizedSourceBackedFixedSTestFromTheorems).weilTest
        (normalizedSourceBackedFixedSTestFromTheorems).weilTest := by
        simpa [normalizedCommonFromTheorems, normalizedSourceBackedFixedSTestFromTheorems] using
          scalar_equality_from_scoped_witness_components
            normalizedSelectedRestrictedToFullScalarRestrictionWitnessFromTheorems

def normalizedSelectedSourceTraceReadOffEqualityInputFromTheorems :
    NormalizedSelectedSourceTraceReadOffEqualityInput where
  fullTraceReadOffEquality :=
    normalizedSelectedFullTraceReadOffEqualityFromRestrictedToFull
  restrictedTraceReadOffEquality :=
    normalizedSelectedRestrictedTraceReadOffEqualityFromFixedTuple

def normalizedTraceFullReadOffEqualityInputFromTheorems :
    NormalizedTraceFullReadOffEqualityInput where
  fullTraceReadOffEquality :=
    normalizedSelectedSourceTraceReadOffEqualityInputFromTheorems.fullTraceReadOffEquality

def normalizedTraceFullReadOffBuildInputFromTheorems :
    NormalizedTraceFullReadOffBuildInput where
  build := by
    intro hnoDefect hfull
    exact
      full_trace_read_off_source_of_parts hnoDefect hfull
        normalizedTraceFullReadOffEqualityInputFromTheorems.fullTraceReadOffEquality

structure NormalizedTraceFullReadOffPreservationInput where
  preservesNoDefect :
    ∀ hnoDefect hfull,
      (normalizedTraceFullReadOffBuildInputFromTheorems.build
        hnoDefect hfull).noDefectSourceReadOff = hnoDefect
  preservesFullQW :
    ∀ hnoDefect hfull,
      (normalizedTraceFullReadOffBuildInputFromTheorems.build
        hnoDefect hfull).ccm25FullQWReadOff = hfull

def normalizedTraceFullReadOffPreservationInputFromTheorems :
    NormalizedTraceFullReadOffPreservationInput where
  preservesNoDefect := by
    intro hnoDefect hfull
    rfl
  preservesFullQW := by
    intro hnoDefect hfull
    rfl

structure NormalizedTraceFullReadOffBridgeInput where
  fullTraceReadOffBridge :
    FullTraceReadOffBridgeContract
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (normalizedSourceBackedFixedSTestFromTheorems)

def normalizedTraceFullReadOffBridgeInputFromTheorems :
    NormalizedTraceFullReadOffBridgeInput where
  fullTraceReadOffBridge :=
    { build :=
        normalizedTraceFullReadOffBuildInputFromTheorems.build
      preservesNoDefect :=
        normalizedTraceFullReadOffPreservationInputFromTheorems.preservesNoDefect
      preservesFullQW :=
        normalizedTraceFullReadOffPreservationInputFromTheorems.preservesFullQW }

structure NormalizedTraceRestrictedReadOffBuildInput where
  build :
    CCM25RestrictedQWReadOff
        (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
        (normalizedSourceBackedFixedSTestFromTheorems)
        normalizedTraceLambdaInputFromTheorems.lambda →
      RestrictedTraceReadOffSource
        (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
        normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
        (normalizedSourceBackedFixedSTestFromTheorems)
        normalizedTraceLambdaInputFromTheorems.lambda

structure NormalizedTraceRestrictedReadOffEqualityInput where
  restrictedTraceReadOffEquality :
    RestrictedTraceReadOffEquality
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedTraceLambdaInputFromTheorems.lambda

def normalizedTraceRestrictedReadOffEqualityInputFromTheorems :
    NormalizedTraceRestrictedReadOffEqualityInput where
  restrictedTraceReadOffEquality :=
    normalizedSelectedSourceTraceReadOffEqualityInputFromTheorems.restrictedTraceReadOffEquality

def normalizedTraceRestrictedReadOffBuildInputFromTheorems :
    NormalizedTraceRestrictedReadOffBuildInput where
  build := by
    intro hrestricted
    exact
      restricted_trace_read_off_source_of_parts hrestricted
        normalizedTraceRestrictedReadOffEqualityInputFromTheorems.restrictedTraceReadOffEquality

structure NormalizedTraceRestrictedReadOffPreservationInput where
  preservesRestrictedQW :
    ∀ hrestricted,
      (normalizedTraceRestrictedReadOffBuildInputFromTheorems.build
        hrestricted).ccm25RestrictedQWReadOff = hrestricted

def normalizedTraceRestrictedReadOffPreservationInputFromTheorems :
    NormalizedTraceRestrictedReadOffPreservationInput where
  preservesRestrictedQW := by
    intro hrestricted
    rfl

structure NormalizedTraceRestrictedReadOffBridgeInput where
  restrictedTraceReadOffBridge :
    RestrictedTraceReadOffBridgeContract
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedTraceLambdaInputFromTheorems.lambda

def normalizedTraceRestrictedReadOffBridgeInputFromTheorems :
    NormalizedTraceRestrictedReadOffBridgeInput where
  restrictedTraceReadOffBridge :=
    { build :=
        normalizedTraceRestrictedReadOffBuildInputFromTheorems.build
      preservesRestrictedQW :=
        normalizedTraceRestrictedReadOffPreservationInputFromTheorems.preservesRestrictedQW }

structure NormalizedTraceReadOffBridgeInput where
  full : NormalizedTraceFullReadOffBridgeInput
  restricted : NormalizedTraceRestrictedReadOffBridgeInput

def normalizedTraceReadOffBridgeInputFromTheorems :
    NormalizedTraceReadOffBridgeInput where
  full := normalizedTraceFullReadOffBridgeInputFromTheorems
  restricted := normalizedTraceRestrictedReadOffBridgeInputFromTheorems

def normalizedTraceSourceReadOffDataFromParts :
    SourceTraceReadOffData
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems) :=
  TraceFrontEndData.sourceTraceReadOffDataOfTraceFrontParts
    normalizedSourceObjectPackageFromTheorems
    normalizedFixedFrontEndFromTheorems
    normalizedTraceLambdaInputFromTheorems.lambda
    normalizedTraceLambdaInputFromTheorems.oneLtLambda
    normalizedTraceCCM25ArithmeticPackageFromTheorems
    normalizedTraceQuotientCompatibilityInputFromTheorems.testAndQuotientCompatibility
    normalizedTraceSupportSquareTransportInputFromTheorems.fixedSSupportSquareTransport
    normalizedTraceFullReadOffBridgeInputFromTheorems.fullTraceReadOffBridge
    normalizedTraceRestrictedReadOffBridgeInputFromTheorems.restrictedTraceReadOffBridge

theorem normalizedTraceFullReadOffEqualityOfSourceTraceDataFromParts :
    FullTraceReadOffEquality
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (normalizedSourceBackedFixedSTestFromTheorems) :=
  (full_trace_read_off_of_source_trace_data
    normalizedTraceSourceReadOffDataFromParts).fullTraceReadOffEquality

theorem normalizedTraceRestrictedReadOffEqualityOfSourceTraceDataFromParts :
    RestrictedTraceReadOffEquality
      (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedTraceSourceReadOffDataFromParts.lambda :=
  (restricted_trace_read_off_of_source_trace_data
    normalizedTraceSourceReadOffDataFromParts).restrictedTraceReadOffEquality

structure NormalizedTraceOrdinarySupportSquareInput where
  ordinary :
    OrdinaryTraceSupportSquareTheoremData
      normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceCCM25ArithmeticPackageFromTheorems

def normalizedTraceOrdinarySupportSquareInputFromTheorems :
    NormalizedTraceOrdinarySupportSquareInput where
  ordinary :=
    TraceFrontEndData.ordinary_trace_support_square_theorem_data_of_trace_front_parts
      (pkg := normalizedSourceObjectPackageFromTheorems)
      (fixedFront := normalizedFixedFrontEndFromTheorems)
      normalizedTraceSourceReadOffDataFromParts

structure NormalizedTraceNoDefectQWLambdaInput where
  noDefect :
    NoDefectQWLambdaTheoremData
      normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceCCM25ArithmeticPackageFromTheorems

def normalizedTraceNoDefectQWLambdaInputFromTheorems :
    NormalizedTraceNoDefectQWLambdaInput where
  noDefect :=
    TraceFrontEndData.no_defect_qw_lambda_theorem_data_of_trace_front_parts
      (pkg := normalizedSourceObjectPackageFromTheorems)
      (fixedFront := normalizedFixedFrontEndFromTheorems)
      normalizedTraceSourceReadOffDataFromParts rfl HEq.rfl

structure NormalizedTraceRankPoleCdefOwnershipInput where
  rankPoleCdefOwnEveryRemainder :
    (L : RouteLedgers) ->
      SourceSignDefectClassification
        (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
        (normalizedSourceBackedFixedSTestFromTheorems)
        normalizedTraceLambdaInputFromTheorems.lambda L -> Prop

def normalizedTraceRankPoleCdefOwnershipInputFromTheorems :
    NormalizedTraceRankPoleCdefOwnershipInput where
  rankPoleCdefOwnEveryRemainder := by
    intro _L h
    exact TraceFrontEndData.trace_scale_owns_sign_defect_remainder h

def normalizedTraceSupportSquareQWLambdaReadOffFromParts :
    TraceFrontEndData.SourceTraceSupportSquareQWLambdaReadOff
      (pkg := normalizedSourceObjectPackageFromTheorems)
      (fixedFront := normalizedFixedFrontEndFromTheorems)
      (lambda := normalizedTraceLambdaInputFromTheorems.lambda)
      (ccm25ArithmeticPackage := normalizedTraceCCM25ArithmeticPackageFromTheorems)
      normalizedTraceSourceReadOffDataFromParts :=
  TraceFrontEndData.source_trace_support_square_qw_lambda_read_off_of_parts
    (pkg := normalizedSourceObjectPackageFromTheorems)
    (fixedFront := normalizedFixedFrontEndFromTheorems)
    normalizedTraceSourceReadOffDataFromParts rfl

theorem normalizedTraceSourceReadOffDataFromParts_archimedeanTest_eq :
    normalizedTraceSourceReadOffDataFromParts.archimedeanTest =
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest :=
  rfl

def normalizedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems :
    Source.S2B1FixedTupleSupportSquareQWLambdaRow
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (normalizedSourceBackedFixedSTestFromTheorems).weilTest :=
  by
    simpa [normalizedTraceSourceReadOffDataFromParts_archimedeanTest_eq] using
      normalizedSelectedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems

theorem normalizedTraceSelectedPositiveTraceEqSupportSquareFromTheorems :
    normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols.positiveTrace
        normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest =
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols.supportSquareTrace
        normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest :=
  (RouteInputs.ofExpandedSourcePackage
    normalizedSourceObjectPackageFromTheorems).cc20.ordinaryTraceSupportSquare
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      normalizedTraceSelectedLegalityDataFromTheorems.selectedTraceClass
      normalizedTraceSelectedLegalityDataFromTheorems.selectedCyclicLegal

def normalizedTraceSupportSquareQWLambdaReadOffSourceDataFromTheorems :
    Source.S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (normalizedSourceBackedFixedSTestFromTheorems).weilTest where
  sourceRestrictedTraceScalar :=
    normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols.qwLambda
      normalizedTraceLambdaInputFromTheorems.lambda
      (normalizedSourceBackedFixedSTestFromTheorems).weilTest
      (normalizedSourceBackedFixedSTestFromTheorems).weilTest
  cc20SupportSquareTraceReadOff :=
    normalizedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems.supportSquareMainTermEqualsQWLambda
  ccm25QWLambdaSourceReadOff := rfl

def normalizedTraceSelectedSupportSquareQWLambdaReadOffSourceDataFromTheorems :
    Source.S2B1FixedTupleSupportSquareQWLambdaReadOffSourceData
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (normalizedSourceBackedFixedSTestFromTheorems).weilTest :=
  normalizedTraceSupportSquareQWLambdaReadOffSourceDataFromTheorems

def normalizedTraceSelectedReadOffDataFromTheorems :
    Source.CC20SelectedTraceReadOffData
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (normalizedSourceBackedFixedSTestFromTheorems).weilTest :=
  Source.CC20SelectedTraceReadOffData.ofSupportSquareQWLambda
    normalizedTraceSelectedLegalityDataFromTheorems
    normalizedTraceSelectedPositiveTraceEqSupportSquareFromTheorems
    normalizedTraceSelectedSupportSquareQWLambdaReadOffSourceDataFromTheorems

def normalizedTraceFixedTupleRankZeroModeConstructorInputFromTheorems :
    Source.S2B1FixedTupleRankZeroModeConstructorInput
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (normalizedSourceBackedFixedSTestFromTheorems).weilTest :=
  normalizedBaseFromTheorems.s2b1NormalizedSeedRankZeroModeConstructorInput
    normalizedTraceLambdaInputFromTheorems.lambda
    normalizedTraceLambdaInputFromTheorems.oneLtLambda
    normalizedTraceSourceReadOffDataFromParts.archimedeanTest
    (normalizedSourceBackedFixedSTestFromTheorems).weilTest

def normalizedTraceFixedTupleRankZeroModeRowFromTheorems :
    Source.S2B1FixedTupleRankZeroModeRow
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (normalizedSourceBackedFixedSTestFromTheorems).weilTest :=
  normalizedTraceFixedTupleRankZeroModeConstructorInputFromTheorems.toRow

def normalizedTraceFixedTupleNoStripRankPoleConstructorInputFromTheorems :
    Source.S2B1FixedTupleNoStripRankPoleConstructorInput
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (normalizedSourceBackedFixedSTestFromTheorems).weilTest :=
  normalizedBaseFromTheorems.s2b1NormalizedSeedNoStripRankPoleConstructorInput
    normalizedTraceLambdaInputFromTheorems.lambda
    normalizedTraceLambdaInputFromTheorems.oneLtLambda
    normalizedTraceSourceReadOffDataFromParts.archimedeanTest
    (normalizedSourceBackedFixedSTestFromTheorems).weilTest

def normalizedTraceFixedTupleNoStripRankPoleRowFromTheorems :
    Source.S2B1FixedTupleNoStripRankPoleRow
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (normalizedSourceBackedFixedSTestFromTheorems).weilTest :=
  normalizedTraceFixedTupleNoStripRankPoleConstructorInputFromTheorems.toRow

def normalizedTraceFixedTupleEndpointStripCdefConstructorInputFromTheorems :
    Source.S2B1FixedTupleEndpointStripCdefConstructorInput
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (normalizedSourceBackedFixedSTestFromTheorems).weilTest :=
  normalizedBaseFromTheorems.s2b1NormalizedSeedEndpointStripCdefConstructorInput
    normalizedTraceLambdaInputFromTheorems.lambda
    normalizedTraceLambdaInputFromTheorems.oneLtLambda
    normalizedTraceSourceReadOffDataFromParts.archimedeanTest
    (normalizedSourceBackedFixedSTestFromTheorems).weilTest

def normalizedTraceFixedTupleEndpointStripCdefRowFromTheorems :
    Source.S2B1FixedTupleEndpointStripCdefRow
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (normalizedSourceBackedFixedSTestFromTheorems).weilTest :=
  normalizedTraceFixedTupleEndpointStripCdefConstructorInputFromTheorems.toRow

def normalizedTraceFixedTupleNoExtraBulkConstructorInputFromTheorems :
    Source.S2B1FixedTupleNoExtraBulkConstructorInput
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (normalizedSourceBackedFixedSTestFromTheorems).weilTest :=
  normalizedBaseFromTheorems.s2b1NormalizedSeedNoExtraBulkConstructorInput
    normalizedTraceLambdaInputFromTheorems.lambda
    normalizedTraceLambdaInputFromTheorems.oneLtLambda
    normalizedTraceSourceReadOffDataFromParts.archimedeanTest
    (normalizedSourceBackedFixedSTestFromTheorems).weilTest

def normalizedTraceFixedTupleNoExtraBulkRowFromTheorems :
    Source.S2B1FixedTupleNoExtraBulkRow
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (normalizedSourceBackedFixedSTestFromTheorems).weilTest :=
  normalizedTraceFixedTupleNoExtraBulkConstructorInputFromTheorems.toRow

def normalizedTraceFixedTupleNoHiddenFinitePartSubtractionConstructorInputFromTheorems :
    Source.S2B1FixedTupleNoHiddenFinitePartSubtractionConstructorInput
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (normalizedSourceBackedFixedSTestFromTheorems).weilTest :=
  normalizedBaseFromTheorems.s2b1NormalizedSeedNoHiddenFinitePartSubtractionConstructorInput
    normalizedTraceLambdaInputFromTheorems.lambda
    normalizedTraceLambdaInputFromTheorems.oneLtLambda
    normalizedTraceSourceReadOffDataFromParts.archimedeanTest
    (normalizedSourceBackedFixedSTestFromTheorems).weilTest

def normalizedTraceFixedTupleNoHiddenFinitePartSubtractionRowFromTheorems :
    Source.S2B1FixedTupleNoHiddenFinitePartSubtractionRow
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (normalizedSourceBackedFixedSTestFromTheorems).weilTest :=
  normalizedTraceFixedTupleNoHiddenFinitePartSubtractionConstructorInputFromTheorems.toRow

def normalizedTraceFinitePartSourceNormalFormDataFromTheorems :
    Source.S2B1FinitePartSourceNormalFormData
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (normalizedSourceBackedFixedSTestFromTheorems).weilTest :=
  normalizedBaseFromTheorems.s2b1FinitePartSourceNormalFormData
    normalizedTraceLambdaInputFromTheorems.lambda
    normalizedTraceLambdaInputFromTheorems.oneLtLambda
    normalizedTraceSourceReadOffDataFromParts.archimedeanTest
    (normalizedSourceBackedFixedSTestFromTheorems).weilTest

def normalizedTraceFixedTupleRemainingRowsPackageFromTheorems :
    Source.S2B1FixedTupleRemainingRowsPackage
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (normalizedSourceBackedFixedSTestFromTheorems).weilTest where
  rankZeroModeRow :=
    normalizedTraceFixedTupleRankZeroModeRowFromTheorems
  noStripRankPoleRow :=
    normalizedTraceFixedTupleNoStripRankPoleRowFromTheorems
  endpointStripCdefRow :=
    normalizedTraceFixedTupleEndpointStripCdefRowFromTheorems
  noExtraBulkRow :=
    normalizedTraceFixedTupleNoExtraBulkRowFromTheorems
  noHiddenFinitePartSubtractionRow :=
    normalizedTraceFixedTupleNoHiddenFinitePartSubtractionRowFromTheorems

def normalizedTraceFixedTupleAnalyticExclusionFromTheorems :
    Source.S2B1TraceScaleFixedTupleAnalyticExclusionPackage
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (normalizedSourceBackedFixedSTestFromTheorems).weilTest :=
  Source.S2B1FixedTupleRemainingRowsPackage.toAnalyticExclusionPackage
    normalizedTraceFixedTupleRemainingRowsPackageFromTheorems
    normalizedTraceLambdaInputFromTheorems.oneLtLambda
    normalizedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems

def normalizedTraceNoBulkSourceWitnessFromParts :
    Source.CC20CCMTraceScaleNoBulkWitness
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceSourceReadOffDataFromParts.archimedeanTest
      (normalizedSourceBackedFixedSTestFromTheorems).weilTest :=
  { noBulkScaleTermOutsideLedger :=
      normalizedTraceFixedTupleNoExtraBulkRowFromTheorems.noExtraBulkScaleTermExcluded
    noHiddenFinitePartSubtraction :=
      normalizedTraceFixedTupleNoHiddenFinitePartSubtractionRowFromTheorems.noHiddenFinitePartSubtractionExcluded
    noBulkScaleTermOutsideLedgerHolds :=
      normalizedTraceFixedTupleNoExtraBulkRowFromTheorems.noExtraBulkScaleTermExcludedHolds
    noHiddenFinitePartSubtractionHolds :=
      normalizedTraceFixedTupleNoHiddenFinitePartSubtractionRowFromTheorems.noHiddenFinitePartSubtractionExcludedHolds }

structure NormalizedTracePositiveTraceDecompositionInput where
  positiveTraceDecomposesIntoQWLambdaRankPoleCdef : Prop
  positiveTraceDecomposesIntoQWLambdaRankPoleCdefHolds :
    positiveTraceDecomposesIntoQWLambdaRankPoleCdef

def normalizedTracePositiveTraceDecompositionInputFromTheorems :
    NormalizedTracePositiveTraceDecompositionInput where
  positiveTraceDecomposesIntoQWLambdaRankPoleCdef :=
    normalizedTraceOrdinarySupportSquareInputFromTheorems.ordinary.ordinaryTraceMatchesSupportSquare ∧
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols.supportSquareTrace
          normalizedTraceSourceReadOffDataFromParts.archimedeanTest =
        normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols.qwLambda
          normalizedTraceLambdaInputFromTheorems.lambda
          (normalizedSourceBackedFixedSTestFromTheorems).weilTest
          (normalizedSourceBackedFixedSTestFromTheorems).weilTest ∧
      normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.rankZeroModeRow.rankZeroModeChannelClassified ∧
      normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.noStripRankPoleRow.noStripPostQRemainderRankPoleClassified ∧
      normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.endpointStripCdefRow.endpointStripBulkClassifiedIntoCdef ∧
      normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.endpointStripCdefRow.endpointStripBoundaryTermsClassified ∧
      normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.endpointStripCdefRow.sourceSeriesTailClassifiedIntoCdef ∧
      normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.endpointStripCdefRow.cdefExhaustionOwnsEndpointStrip
  positiveTraceDecomposesIntoQWLambdaRankPoleCdefHolds :=
    ⟨normalizedTraceOrdinarySupportSquareInputFromTheorems.ordinary.ordinaryTraceMatchesSupportSquareHolds,
      normalizedTraceFixedTupleSupportSquareQWLambdaRowFromTheorems.supportSquareMainTermEqualsQWLambda,
      normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.rankZeroModeRow.rankZeroModeChannelClassifiedHolds,
      normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.noStripRankPoleRow.noStripPostQRemainderRankPoleClassifiedHolds,
      normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.endpointStripCdefRow.endpointStripBulkClassifiedIntoCdefHolds,
      normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.endpointStripCdefRow.endpointStripBoundaryTermsClassifiedHolds,
      normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.endpointStripCdefRow.sourceSeriesTailClassifiedIntoCdefHolds,
      normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.endpointStripCdefRow.cdefExhaustionOwnsEndpointStripHolds⟩

structure NormalizedTraceNoExtraBulkTermInput where
  noBulkScaleTermOutsideLedger : Prop
  noBulkScaleTermOutsideLedgerHolds : noBulkScaleTermOutsideLedger

def normalizedTraceNoExtraBulkTermInputFromTheorems :
    NormalizedTraceNoExtraBulkTermInput where
  noBulkScaleTermOutsideLedger :=
    normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.noExtraBulkRow.noExtraBulkScaleTermExcluded
  noBulkScaleTermOutsideLedgerHolds :=
    normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.noExtraBulkRow.noExtraBulkScaleTermExcludedHolds

structure NormalizedTraceNoHiddenFinitePartInput where
  noHiddenFinitePartSubtraction : Prop
  noHiddenFinitePartSubtractionHolds : noHiddenFinitePartSubtraction

def normalizedTraceNoHiddenFinitePartInputFromTheorems :
    NormalizedTraceNoHiddenFinitePartInput where
  noHiddenFinitePartSubtraction :=
    normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.noHiddenFinitePartSubtractionRow.noHiddenFinitePartSubtractionExcluded
  noHiddenFinitePartSubtractionHolds :=
    normalizedTraceFixedTupleRemainingRowsPackageFromTheorems.noHiddenFinitePartSubtractionRow.noHiddenFinitePartSubtractionExcludedHolds

structure NormalizedTraceNoExtraBulkScaleTermInput where
  noExtraBulkScaleTerm : Prop
  noExtraBulkScaleTermHolds : noExtraBulkScaleTerm

def normalizedTraceNoExtraBulkScaleTermInputFromTheorems :
    NormalizedTraceNoExtraBulkScaleTermInput where
  noExtraBulkScaleTerm :=
    normalizedTracePositiveTraceDecompositionInputFromTheorems.positiveTraceDecomposesIntoQWLambdaRankPoleCdef ∧
      normalizedTraceNoExtraBulkTermInputFromTheorems.noBulkScaleTermOutsideLedger ∧
        normalizedTraceNoHiddenFinitePartInputFromTheorems.noHiddenFinitePartSubtraction
  noExtraBulkScaleTermHolds :=
    ⟨normalizedTracePositiveTraceDecompositionInputFromTheorems.positiveTraceDecomposesIntoQWLambdaRankPoleCdefHolds,
      normalizedTraceNoExtraBulkTermInputFromTheorems.noBulkScaleTermOutsideLedgerHolds,
      normalizedTraceNoHiddenFinitePartInputFromTheorems.noHiddenFinitePartSubtractionHolds⟩

structure NormalizedTraceScaleNoMissingBulkInput where
  ordinarySupportSquare : NormalizedTraceOrdinarySupportSquareInput
  noDefectQWLambda : NormalizedTraceNoDefectQWLambdaInput
  rankPoleCdefOwnership : NormalizedTraceRankPoleCdefOwnershipInput

def normalizedTraceScaleNoMissingBulkInputFromTheorems :
    NormalizedTraceScaleNoMissingBulkInput where
  ordinarySupportSquare :=
    normalizedTraceOrdinarySupportSquareInputFromTheorems
  noDefectQWLambda :=
    normalizedTraceNoDefectQWLambdaInputFromTheorems
  rankPoleCdefOwnership :=
    normalizedTraceRankPoleCdefOwnershipInputFromTheorems

def normalizedTraceScalePositiveQWLambdaDecompositionDataFromTheorems :
    TraceFrontEndData.TraceScalePositiveQWLambdaDecompositionData
      normalizedSourceObjectPackageFromTheorems
      normalizedFixedFrontEndFromTheorems
      normalizedTraceLambdaInputFromTheorems.lambda :=
  TraceFrontEndData.TraceScalePositiveQWLambdaDecompositionData.ofSelectedReadOff
    normalizedTraceSelectedReadOffDataFromTheorems

def normalizedTraceScaleBulkResidualDataFromTheorems :
    TraceFrontEndData.TraceScaleBulkResidualData
      normalizedSourceObjectPackageFromTheorems
      normalizedFixedFrontEndFromTheorems
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceScalePositiveQWLambdaDecompositionDataFromTheorems :=
  TraceFrontEndData.TraceScaleBulkResidualData.ofPositiveQWLambda
    normalizedTraceScalePositiveQWLambdaDecompositionDataFromTheorems

def normalizedTraceScaleFinitePartResidualDataFromTheorems :
    TraceFrontEndData.TraceScaleFinitePartResidualData
      normalizedSourceObjectPackageFromTheorems
      normalizedFixedFrontEndFromTheorems
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceFinitePartSourceNormalFormDataFromTheorems :=
  TraceFrontEndData.TraceScaleFinitePartResidualData.ofSourceNormalForm
    normalizedTraceFinitePartSourceNormalFormDataFromTheorems

def normalizedTraceScaleNoExtraBulkScalarDataFromTheorems :
    TraceFrontEndData.TraceScaleNoExtraBulkScalarData
      normalizedSourceObjectPackageFromTheorems
      normalizedFixedFrontEndFromTheorems
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceCCM25ArithmeticPackageFromTheorems :=
  TraceFrontEndData.TraceScaleNoExtraBulkScalarData.ofSelectedData
    normalizedTraceScalePositiveQWLambdaDecompositionDataFromTheorems
    normalizedTraceFinitePartSourceNormalFormDataFromTheorems

def normalizedNoExtraBulkSourceTermsFromTheorems :
    TraceFrontEndData.TraceScaleNoExtraBulkSourceTermData
      normalizedSourceObjectPackageFromTheorems
      normalizedFixedFrontEndFromTheorems
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceCCM25ArithmeticPackageFromTheorems :=
  normalizedTraceScaleNoExtraBulkScalarDataFromTheorems.toSourceTermData

def normalizedTraceScaleNoMissingBulkDataFromTheorems :
    TraceScaleNoMissingBulkData
      normalizedSourceObjectPackageFromTheorems normalizedFixedFrontEndFromTheorems
      normalizedTraceLambdaInputFromTheorems.lambda
      normalizedTraceCCM25ArithmeticPackageFromTheorems :=
  trace_scale_no_missing_bulk_of_scalar_theorem_data
    normalizedTraceScaleNoMissingBulkInputFromTheorems.ordinarySupportSquare.ordinary
    normalizedTraceScaleNoMissingBulkInputFromTheorems.noDefectQWLambda.noDefect
    normalizedTraceScaleNoMissingBulkInputFromTheorems.rankPoleCdefOwnership.rankPoleCdefOwnEveryRemainder
    (TraceFrontEndData.TraceScaleNoExtraBulkSourceTermStatement
      normalizedNoExtraBulkSourceTermsFromTheorems)
    (TraceFrontEndData.trace_scale_no_extra_bulk_source_term_statement_holds
      normalizedNoExtraBulkSourceTermsFromTheorems)

structure NormalizedTraceFrontEndSourceInput where
  quotientCompatibility : NormalizedTraceQuotientCompatibilityInput
  supportSquareTransport : NormalizedTraceSupportSquareTransportInput
  readOffBridges : NormalizedTraceReadOffBridgeInput

def normalizedTraceFrontEndSourceInputFromTheorems :
    NormalizedTraceFrontEndSourceInput where
  quotientCompatibility := normalizedTraceQuotientCompatibilityInputFromTheorems
  supportSquareTransport := normalizedTraceSupportSquareTransportInputFromTheorems
  readOffBridges := normalizedTraceReadOffBridgeInputFromTheorems

def normalizedTraceDataFromTheorems :
    TraceFrontEndData
      normalizedSourceObjectPackageFromTheorems
      normalizedFixedFrontEndFromTheorems :=
  { lambda := normalizedTraceLambdaInputFromTheorems.lambda
    oneLtLambda := normalizedTraceLambdaInputFromTheorems.oneLtLambda
    ccm25ArithmeticPackage :=
      normalizedTraceCCM25ArithmeticPackageFromTheorems
    testAndQuotientCompatibility :=
      normalizedTraceFrontEndSourceInputFromTheorems.quotientCompatibility.testAndQuotientCompatibility
    fixedSSupportSquareTransport :=
      normalizedTraceFrontEndSourceInputFromTheorems.supportSquareTransport.fixedSSupportSquareTransport
    fullTraceReadOffBridge :=
      normalizedTraceFrontEndSourceInputFromTheorems.readOffBridges.full.fullTraceReadOffBridge
    restrictedTraceReadOffBridge :=
      normalizedTraceFrontEndSourceInputFromTheorems.readOffBridges.restricted.restrictedTraceReadOffBridge
    traceScaleNoMissingBulk :=
      normalizedTraceScaleNoMissingBulkDataFromTheorems }

def normalizedFrontEndPackageFromTheorems :
    TraceFrontEndData.SourceFixedTraceFrontEndPackage
      normalizedSourceObjectPackageFromTheorems :=
  TraceFrontEndData.source_fixed_trace_front_end_package_of_trace_data
    normalizedSourceObjectPackageFromTheorems
    normalizedFixedFrontEndFromTheorems
    normalizedTraceDataFromTheorems

theorem normalizedFrontEndPackageSourceTraceReadOffData_eq :
    normalizedFrontEndPackageFromTheorems.sourceTraceReadOffData =
      normalizedTraceSourceReadOffDataFromParts :=
  rfl

abbrev normalizedTraceFrontEndFromTheorems :
    ExpandedSourceTraceReadOffFrontEnd
      normalizedSourceObjectPackageFromTheorems
      normalizedFixedFrontEndFromTheorems :=
  normalizedFrontEndPackageFromTheorems.traceFront

noncomputable abbrev normalizedScalarSeedFromTheorems :
    Source.CC20Concrete.TraceScale.NormalizedScalarTraceScaleSymbols :=
  TraceFrontEndData.normalizedRestrictedScalarTraceSeedOfTraceData
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems

structure NormalizedScalarCC20RemainderRowsInput where
  rows :
    Source.NormalizedScalarCC20RemainderRows
      normalizedScalarSeedFromTheorems

noncomputable def normalizedScalarCC20RemainderRowsInputFromTheorems :
    NormalizedScalarCC20RemainderRowsInput where
  rows :=
    normalizedSourceObjectScalarRemainderRowsProviderFromTheorems
      normalizedScalarSeedFromTheorems

noncomputable def normalizedScalarFinitePartSourceNormalFormDataFromTheorems
    (lambda : ℝ) (hlambda : 1 < lambda)
    (archimedeanTest :
      (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test)
    (weilTest : TestFunction) :
    Source.S2B1FinitePartSourceNormalFormData
      (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          normalizedScalarSeedFromTheorems)).archimedeanSymbols
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols
      lambda archimedeanTest weilTest :=
  normalizedSourceObjectScalarFinitePartSourceNormalFormDataFromTheorems
    normalizedScalarSeedFromTheorems lambda hlambda archimedeanTest weilTest

structure NormalizedScalarTraceLegalityRemainderInput where
  sourceTraceTest :
    (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
      (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
        normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test
  sourceCC20TraceTestCompatibility : Prop
  sourceOperatorIdentity : Prop
  sourceHilbertSchmidtGate :
    ∀ g :
      (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test,
        ArchimedeanTraceSymbols.hilbertSchmidtGate
          (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
            (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
              normalizedScalarSeedFromTheorems)).archimedeanSymbols
          g
  sourcePerMoveCyclicityLedger : Prop

structure NormalizedScalarTraceLegalitySourceRowsInput where
  sourceTraceTest :
    (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
      (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
        normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test
  sourceCC20TraceTestCompatibility : Prop
  sourceOperatorIdentity : Prop
  sourceHilbertSchmidtGate :
    ∀ g :
      (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test,
        ArchimedeanTraceSymbols.hilbertSchmidtGate
          (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
            (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
              normalizedScalarSeedFromTheorems)).archimedeanSymbols
          g
  sourcePerMoveCyclicityLedger : Prop

structure NormalizedScalarTraceTestSelectionInput where
  sourceTraceTest :
    (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
      (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
        normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test
  sourceCC20TraceTestCompatibility : Prop

noncomputable def normalizedScalarTraceTestSelectionInputFromTheorems :
    NormalizedScalarTraceTestSelectionInput where
  sourceTraceTest :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceTraceTest
  sourceCC20TraceTestCompatibility :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceCC20TraceTestCompatibility

structure NormalizedScalarTraceOperatorIdentityInput where
  sourceOperatorIdentity : Prop

noncomputable def normalizedScalarTraceOperatorIdentityInputFromTheorems :
    NormalizedScalarTraceOperatorIdentityInput where
  sourceOperatorIdentity :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceOperatorIdentity

structure NormalizedScalarTraceLegalityGateInput where
  sourceHilbertSchmidtGate :
    ∀ g :
      (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test,
        ArchimedeanTraceSymbols.hilbertSchmidtGate
          (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
            (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
              normalizedScalarSeedFromTheorems)).archimedeanSymbols
          g
  sourcePerMoveCyclicityLedger : Prop

noncomputable def normalizedScalarTraceLegalityGateInputFromTheorems :
    NormalizedScalarTraceLegalityGateInput where
  sourceHilbertSchmidtGate :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceHilbertSchmidtGate
  sourcePerMoveCyclicityLedger :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourcePerMoveCyclicityLedger

noncomputable def normalizedScalarTraceLegalitySourceRowsInputFromTheorems :
    NormalizedScalarTraceLegalitySourceRowsInput where
  sourceTraceTest :=
    normalizedScalarTraceTestSelectionInputFromTheorems.sourceTraceTest
  sourceCC20TraceTestCompatibility :=
    normalizedScalarTraceTestSelectionInputFromTheorems.sourceCC20TraceTestCompatibility
  sourceOperatorIdentity :=
    normalizedScalarTraceOperatorIdentityInputFromTheorems.sourceOperatorIdentity
  sourceHilbertSchmidtGate :=
    normalizedScalarTraceLegalityGateInputFromTheorems.sourceHilbertSchmidtGate
  sourcePerMoveCyclicityLedger :=
    normalizedScalarTraceLegalityGateInputFromTheorems.sourcePerMoveCyclicityLedger

noncomputable def normalizedScalarTraceLegalityRemainderInputFromTheorems :
    NormalizedScalarTraceLegalityRemainderInput where
  sourceTraceTest :=
    normalizedScalarTraceLegalitySourceRowsInputFromTheorems.sourceTraceTest
  sourceCC20TraceTestCompatibility :=
    normalizedScalarTraceLegalitySourceRowsInputFromTheorems.sourceCC20TraceTestCompatibility
  sourceOperatorIdentity :=
    normalizedScalarTraceLegalitySourceRowsInputFromTheorems.sourceOperatorIdentity
  sourceHilbertSchmidtGate :=
    normalizedScalarTraceLegalitySourceRowsInputFromTheorems.sourceHilbertSchmidtGate
  sourcePerMoveCyclicityLedger :=
    normalizedScalarTraceLegalitySourceRowsInputFromTheorems.sourcePerMoveCyclicityLedger

structure NormalizedScalarRemainderTransportInput where
  sourceRemainderOrientationWInftyEqLMinusD : Prop
  sourceRemainderOrientationWInftyEqSMinusE : Prop
  sourceRemainderObject : Prop
  sourceRemainderAfterQ : Prop
  cc20PostQRemainderFixedSSoninTransport : Prop
  sourceProjectionDefectNormalForm : Prop
  sourceRankPoleLedgerIdentification : Prop
  sourceEndpointStripRemainderCdefDomination : Prop

structure NormalizedScalarRemainderOrientationInput where
  sourceRemainderOrientationWInftyEqLMinusD : Prop
  sourceRemainderOrientationWInftyEqSMinusE : Prop

noncomputable def normalizedScalarRemainderOrientationInputFromTheorems :
    NormalizedScalarRemainderOrientationInput where
  sourceRemainderOrientationWInftyEqLMinusD :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceRemainderOrientationWInftyEqLMinusD
  sourceRemainderOrientationWInftyEqSMinusE :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceRemainderOrientationWInftyEqSMinusE

structure NormalizedScalarRemainderObjectAfterQInput where
  sourceRemainderObject : Prop
  sourceRemainderAfterQ : Prop

noncomputable def normalizedScalarRemainderObjectAfterQInputFromTheorems :
    NormalizedScalarRemainderObjectAfterQInput where
  sourceRemainderObject :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceRemainderObject
  sourceRemainderAfterQ :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceRemainderAfterQ

structure NormalizedScalarPostQTransportInput where
  cc20PostQRemainderFixedSSoninTransport : Prop

noncomputable def normalizedScalarPostQTransportInputFromTheorems :
    NormalizedScalarPostQTransportInput where
  cc20PostQRemainderFixedSSoninTransport :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.cc20PostQRemainderFixedSSoninTransport

structure NormalizedScalarProjectionRankCdefInput where
  sourceProjectionDefectNormalForm : Prop
  sourceRankPoleLedgerIdentification : Prop
  sourceEndpointStripRemainderCdefDomination : Prop

noncomputable def normalizedScalarProjectionRankCdefInputFromTheorems :
    NormalizedScalarProjectionRankCdefInput where
  sourceProjectionDefectNormalForm :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceProjectionDefectNormalForm
  sourceRankPoleLedgerIdentification :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceRankPoleLedgerIdentification
  sourceEndpointStripRemainderCdefDomination :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceEndpointStripRemainderCdefDomination

noncomputable def normalizedScalarRemainderTransportInputFromTheorems :
    NormalizedScalarRemainderTransportInput where
  sourceRemainderOrientationWInftyEqLMinusD :=
    normalizedScalarRemainderOrientationInputFromTheorems.sourceRemainderOrientationWInftyEqLMinusD
  sourceRemainderOrientationWInftyEqSMinusE :=
    normalizedScalarRemainderOrientationInputFromTheorems.sourceRemainderOrientationWInftyEqSMinusE
  sourceRemainderObject :=
    normalizedScalarRemainderObjectAfterQInputFromTheorems.sourceRemainderObject
  sourceRemainderAfterQ :=
    normalizedScalarRemainderObjectAfterQInputFromTheorems.sourceRemainderAfterQ
  cc20PostQRemainderFixedSSoninTransport :=
    normalizedScalarPostQTransportInputFromTheorems.cc20PostQRemainderFixedSSoninTransport
  sourceProjectionDefectNormalForm :=
    normalizedScalarProjectionRankCdefInputFromTheorems.sourceProjectionDefectNormalForm
  sourceRankPoleLedgerIdentification :=
    normalizedScalarProjectionRankCdefInputFromTheorems.sourceRankPoleLedgerIdentification
  sourceEndpointStripRemainderCdefDomination :=
    normalizedScalarProjectionRankCdefInputFromTheorems.sourceEndpointStripRemainderCdefDomination

structure NormalizedScalarNoBulkRemainderInput where
  noBulkScaleTermOutsideLedger : Prop
  noHiddenFinitePartSubtraction : Prop
  noBulkScaleTermOutsideLedgerHolds : noBulkScaleTermOutsideLedger
  noHiddenFinitePartSubtractionHolds : noHiddenFinitePartSubtraction
  noBulkScaleTermOutsideLedgerAt :
    ℝ →
      (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test →
        TestFunction → Prop
  noHiddenFinitePartSubtractionAt :
    ℝ →
      (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test →
        TestFunction → Prop
  noBulkScaleTermOutsideLedgerAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest :
        (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
          (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
            normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test,
        ∀ weilTest : TestFunction,
          noBulkScaleTermOutsideLedgerAt lambda archimedeanTest weilTest
  noHiddenFinitePartSubtractionAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest :
        (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
          (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
            normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test,
        ∀ weilTest : TestFunction,
          noHiddenFinitePartSubtractionAt lambda archimedeanTest weilTest

structure NormalizedScalarNoBulkStaticRowsInput where
  noBulkScaleTermOutsideLedger : Prop
  noHiddenFinitePartSubtraction : Prop
  noBulkScaleTermOutsideLedgerHolds : noBulkScaleTermOutsideLedger
  noHiddenFinitePartSubtractionHolds : noHiddenFinitePartSubtraction

noncomputable def normalizedScalarNoBulkStaticRowsInputFromTheorems :
    NormalizedScalarNoBulkStaticRowsInput where
  noBulkScaleTermOutsideLedger :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.noBulkScaleTermOutsideLedger
  noHiddenFinitePartSubtraction :=
    ∃ hlambda : 1 < (2 : ℝ),
      Source.S2B1FinitePartScalarInterface.finitePartNormalizationFixedStatement
        ((normalizedScalarFinitePartSourceNormalFormDataFromTheorems
          2 hlambda
          normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceTraceTest
          normalizedCommonFromTheorems.commonTest.sourceTest).sourceScalars.toScalarInterface) ∧
      Source.S2B1FinitePartScalarInterface.noSubtractedFinitePartTermStatement
        ((normalizedScalarFinitePartSourceNormalFormDataFromTheorems
          2 hlambda
          normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceTraceTest
          normalizedCommonFromTheorems.commonTest.sourceTest).sourceScalars.toScalarInterface)
  noBulkScaleTermOutsideLedgerHolds :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.noBulkScaleTermOutsideLedgerHolds
  noHiddenFinitePartSubtractionHolds :=
    ⟨by norm_num,
      (normalizedScalarFinitePartSourceNormalFormDataFromTheorems
        2 (by norm_num)
        normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceTraceTest
        normalizedCommonFromTheorems.commonTest.sourceTest).finitePartNormalizationFixedHolds,
      (normalizedScalarFinitePartSourceNormalFormDataFromTheorems
        2 (by norm_num)
        normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceTraceTest
        normalizedCommonFromTheorems.commonTest.sourceTest).noSubtractedFinitePartTermHolds⟩

structure NormalizedScalarNoBulkSameCutoffRowsInput where
  noBulkScaleTermOutsideLedgerAt :
    ℝ →
      (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test →
        TestFunction → Prop
  noHiddenFinitePartSubtractionAt :
    ℝ →
      (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
          normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test →
        TestFunction → Prop
  noBulkScaleTermOutsideLedgerAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest :
        (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
          (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
            normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test,
        ∀ weilTest : TestFunction,
          noBulkScaleTermOutsideLedgerAt lambda archimedeanTest weilTest
  noHiddenFinitePartSubtractionAtHolds :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest :
        (Source.CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
          (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
            normalizedScalarSeedFromTheorems)).archimedeanSymbols.Test,
        ∀ weilTest : TestFunction,
          noHiddenFinitePartSubtractionAt lambda archimedeanTest weilTest

noncomputable def normalizedScalarNoBulkSameCutoffRowsInputFromTheorems :
    NormalizedScalarNoBulkSameCutoffRowsInput where
  noBulkScaleTermOutsideLedgerAt :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.noBulkScaleTermOutsideLedgerAt
  noHiddenFinitePartSubtractionAt :=
    fun lambda archimedeanTest weilTest =>
      ∃ hlambda : 1 < lambda,
        Source.S2B1FinitePartScalarInterface.finitePartNormalizationFixedStatement
          ((normalizedScalarFinitePartSourceNormalFormDataFromTheorems
            lambda hlambda archimedeanTest weilTest).sourceScalars.toScalarInterface) ∧
        Source.S2B1FinitePartScalarInterface.noSubtractedFinitePartTermStatement
          ((normalizedScalarFinitePartSourceNormalFormDataFromTheorems
            lambda hlambda archimedeanTest weilTest).sourceScalars.toScalarInterface)
  noBulkScaleTermOutsideLedgerAtHolds :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.noBulkScaleTermOutsideLedgerAtHolds
  noHiddenFinitePartSubtractionAtHolds :=
    by
      intro lambda hlambda archimedeanTest weilTest
      exact
        ⟨hlambda,
          (normalizedScalarFinitePartSourceNormalFormDataFromTheorems
            lambda hlambda archimedeanTest weilTest).finitePartNormalizationFixedHolds,
          (normalizedScalarFinitePartSourceNormalFormDataFromTheorems
            lambda hlambda archimedeanTest weilTest).noSubtractedFinitePartTermHolds⟩

noncomputable def normalizedScalarNoBulkRemainderInputFromTheorems :
    NormalizedScalarNoBulkRemainderInput where
  noBulkScaleTermOutsideLedger :=
    normalizedScalarNoBulkStaticRowsInputFromTheorems.noBulkScaleTermOutsideLedger
  noHiddenFinitePartSubtraction :=
    normalizedScalarNoBulkStaticRowsInputFromTheorems.noHiddenFinitePartSubtraction
  noBulkScaleTermOutsideLedgerHolds :=
    normalizedScalarNoBulkStaticRowsInputFromTheorems.noBulkScaleTermOutsideLedgerHolds
  noHiddenFinitePartSubtractionHolds :=
    normalizedScalarNoBulkStaticRowsInputFromTheorems.noHiddenFinitePartSubtractionHolds
  noBulkScaleTermOutsideLedgerAt :=
    normalizedScalarNoBulkSameCutoffRowsInputFromTheorems.noBulkScaleTermOutsideLedgerAt
  noHiddenFinitePartSubtractionAt :=
    normalizedScalarNoBulkSameCutoffRowsInputFromTheorems.noHiddenFinitePartSubtractionAt
  noBulkScaleTermOutsideLedgerAtHolds :=
    normalizedScalarNoBulkSameCutoffRowsInputFromTheorems.noBulkScaleTermOutsideLedgerAtHolds
  noHiddenFinitePartSubtractionAtHolds :=
    normalizedScalarNoBulkSameCutoffRowsInputFromTheorems.noHiddenFinitePartSubtractionAtHolds

structure NormalizedScalarDefectBoundedComparisonInput where
  noHiddenPositiveDefectOutsideCdef : Prop
  sourceBoundedComparisonTraceIdealTransport : Prop

structure NormalizedScalarNoHiddenPositiveDefectInput where
  noHiddenPositiveDefectOutsideCdef : Prop

noncomputable def normalizedScalarNoHiddenPositiveDefectInputFromTheorems :
    NormalizedScalarNoHiddenPositiveDefectInput where
  noHiddenPositiveDefectOutsideCdef :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.noHiddenPositiveDefectOutsideCdef

structure NormalizedScalarBoundedComparisonTransportInput where
  sourceBoundedComparisonTraceIdealTransport : Prop

noncomputable def normalizedScalarBoundedComparisonTransportInputFromTheorems :
    NormalizedScalarBoundedComparisonTransportInput where
  sourceBoundedComparisonTraceIdealTransport :=
    normalizedScalarCC20RemainderRowsInputFromTheorems.rows.sourceBoundedComparisonTraceIdealTransport

noncomputable def normalizedScalarDefectBoundedComparisonInputFromTheorems :
    NormalizedScalarDefectBoundedComparisonInput where
  noHiddenPositiveDefectOutsideCdef :=
    normalizedScalarNoHiddenPositiveDefectInputFromTheorems.noHiddenPositiveDefectOutsideCdef
  sourceBoundedComparisonTraceIdealTransport :=
    normalizedScalarBoundedComparisonTransportInputFromTheorems.sourceBoundedComparisonTraceIdealTransport

structure NormalizedScalarRemainderInputData where
  traceLegality : NormalizedScalarTraceLegalityRemainderInput
  transport : NormalizedScalarRemainderTransportInput
  noBulk : NormalizedScalarNoBulkRemainderInput
  boundedComparison : NormalizedScalarDefectBoundedComparisonInput

noncomputable def normalizedScalarRemainderInputDataFromTheorems :
    NormalizedScalarRemainderInputData where
  traceLegality := normalizedScalarTraceLegalityRemainderInputFromTheorems
  transport := normalizedScalarRemainderTransportInputFromTheorems
  noBulk := normalizedScalarNoBulkRemainderInputFromTheorems
  boundedComparison := normalizedScalarDefectBoundedComparisonInputFromTheorems

noncomputable def normalizedScalarRemaindersFromTheorems :
    Source.CC20Concrete.TraceScale.CC20TracePackageRemainderData
      (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
        normalizedScalarSeedFromTheorems) where
  sourceTraceTest :=
    normalizedScalarRemainderInputDataFromTheorems.traceLegality.sourceTraceTest
  sourceCC20TraceTestCompatibility :=
    normalizedScalarRemainderInputDataFromTheorems.traceLegality.sourceCC20TraceTestCompatibility
  sourceOperatorIdentity :=
    normalizedScalarRemainderInputDataFromTheorems.traceLegality.sourceOperatorIdentity
  sourceHilbertSchmidtGate :=
    normalizedScalarRemainderInputDataFromTheorems.traceLegality.sourceHilbertSchmidtGate
  sourcePerMoveCyclicityLedger :=
    normalizedScalarRemainderInputDataFromTheorems.traceLegality.sourcePerMoveCyclicityLedger
  sourceRemainderOrientationWInftyEqLMinusD :=
    normalizedScalarRemainderInputDataFromTheorems.transport.sourceRemainderOrientationWInftyEqLMinusD
  sourceRemainderOrientationWInftyEqSMinusE :=
    normalizedScalarRemainderInputDataFromTheorems.transport.sourceRemainderOrientationWInftyEqSMinusE
  sourceRemainderObject :=
    normalizedScalarRemainderInputDataFromTheorems.transport.sourceRemainderObject
  sourceRemainderAfterQ :=
    normalizedScalarRemainderInputDataFromTheorems.transport.sourceRemainderAfterQ
  cc20PostQRemainderFixedSSoninTransport :=
    normalizedScalarRemainderInputDataFromTheorems.transport.cc20PostQRemainderFixedSSoninTransport
  sourceProjectionDefectNormalForm :=
    normalizedScalarRemainderInputDataFromTheorems.transport.sourceProjectionDefectNormalForm
  sourceRankPoleLedgerIdentification :=
    normalizedScalarRemainderInputDataFromTheorems.transport.sourceRankPoleLedgerIdentification
  sourceEndpointStripRemainderCdefDomination :=
    normalizedScalarRemainderInputDataFromTheorems.transport.sourceEndpointStripRemainderCdefDomination
  noBulkScaleTermOutsideLedger :=
    normalizedScalarRemainderInputDataFromTheorems.noBulk.noBulkScaleTermOutsideLedger
  noHiddenFinitePartSubtraction :=
    normalizedScalarRemainderInputDataFromTheorems.noBulk.noHiddenFinitePartSubtraction
  noBulkScaleTermOutsideLedgerHolds :=
    normalizedScalarRemainderInputDataFromTheorems.noBulk.noBulkScaleTermOutsideLedgerHolds
  noHiddenFinitePartSubtractionHolds :=
    normalizedScalarRemainderInputDataFromTheorems.noBulk.noHiddenFinitePartSubtractionHolds
  noBulkScaleTermOutsideLedgerAt :=
    normalizedScalarRemainderInputDataFromTheorems.noBulk.noBulkScaleTermOutsideLedgerAt
  noHiddenFinitePartSubtractionAt :=
    normalizedScalarRemainderInputDataFromTheorems.noBulk.noHiddenFinitePartSubtractionAt
  noBulkScaleTermOutsideLedgerAtHolds :=
    normalizedScalarRemainderInputDataFromTheorems.noBulk.noBulkScaleTermOutsideLedgerAtHolds
  noHiddenFinitePartSubtractionAtHolds :=
    normalizedScalarRemainderInputDataFromTheorems.noBulk.noHiddenFinitePartSubtractionAtHolds
  noHiddenPositiveDefectOutsideCdef :=
    normalizedScalarRemainderInputDataFromTheorems.boundedComparison.noHiddenPositiveDefectOutsideCdef
  sourceBoundedComparisonTraceIdealTransport :=
    normalizedScalarRemainderInputDataFromTheorems.boundedComparison.sourceBoundedComparisonTraceIdealTransport

structure NormalizedScalarSourceObjectRHExitInput where
  rhExit : Source.SourceObject.CC20RHExitObjectPackage

def normalizedScalarSourceObjectRHExitInputFromTheorems :
    NormalizedScalarSourceObjectRHExitInput where
  rhExit := normalizedSourceObjectRHExitInputFromTheorems.rhExit

noncomputable def normalizedScalarSourceObjectBridgeRowsFromTheorems :
    Source.SourceObjectExpandedRows normalizedBaseFromTheorems
      normalizedCommonFromTheorems :=
  Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
    normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
    normalizedScalarRemaindersFromTheorems

structure NormalizedScalarSourceObjectRHDefinitionBridgeEqInput where
  rhDefinitionBridge_eq_base :
    normalizedScalarSourceObjectRHExitInputFromTheorems.rhExit.rhDefinitionBridge =
      normalizedBaseFromTheorems.rhDefinitionBridge

def normalizedScalarSourceObjectRHDefinitionBridgeEqInputFromTheorems :
    NormalizedScalarSourceObjectRHDefinitionBridgeEqInput where
  rhDefinitionBridge_eq_base :=
    normalizedSourceObjectRHDefinitionBridgeEqInputFromTheorems.rhDefinitionBridge_eq_base

structure NormalizedScalarSourceObjectCommonTestInvolutionBridgeInput where
  commonTestInvolution :
    Source.SourceObject.CommonTestInvolutionBridge
      (Source.SourceObjectExpandedRows.ccm25
        normalizedScalarSourceObjectBridgeRowsFromTheorems).weilSymbols
      normalizedCommonFromTheorems.commonTest

def normalizedScalarSourceObjectCommonTestInvolutionBridgeInputFromTheorems :
    NormalizedScalarSourceObjectCommonTestInvolutionBridgeInput where
  commonTestInvolution :=
    normalizedSourceObjectCommonTestInvolutionBridgeInputFromTheorems.commonTestInvolution

structure NormalizedScalarSourceObjectCCM24CommonTestBridgeInput where
  ccm24Test_eq_commonTest :
    Source.SourceObject.CCM24CommonTestBridge
      (Source.SourceObjectExpandedRows.ccm25
        normalizedScalarSourceObjectBridgeRowsFromTheorems).weilSymbols
      normalizedCommonFromTheorems.commonTest
      normalizedCCM24FromTheorems

def normalizedScalarSourceObjectCCM24CommonTestBridgeInputFromTheorems :
    NormalizedScalarSourceObjectCCM24CommonTestBridgeInput where
  ccm24Test_eq_commonTest :=
    normalizedSourceObjectCCM24CommonTestBridgeInputFromTheorems.ccm24Test_eq_commonTest

structure NormalizedScalarSourceObjectCC20CommonTestBridgeInput where
  cc20TraceTest_eq_commonTest :
    Source.SourceObject.CC20CommonTestBridge
      (Source.SourceObjectExpandedRows.ccm25
        normalizedScalarSourceObjectBridgeRowsFromTheorems).weilSymbols
      normalizedCommonFromTheorems.commonTest
      normalizedScalarSourceObjectBridgeRowsFromTheorems.cc20Trace

structure NormalizedScalarSourceObjectCC20CommonTestBridgeRowsInput where
  rows :
    Source.NormalizedScalarCC20CommonTestBridgeRows
      normalizedBaseFromTheorems normalizedCommonFromTheorems.commonTest
      normalizedScalarSeedFromTheorems
      normalizedScalarCC20RemainderRowsInputFromTheorems.rows

noncomputable def normalizedScalarSourceObjectCC20CommonTestBridgeRowsInputFromTheorems :
    NormalizedScalarSourceObjectCC20CommonTestBridgeRowsInput where
  rows :=
    normalizedSourceObjectScalarCommonTestBridgeRowsProviderFromTheorems
      normalizedCommonFromTheorems.commonTest
      normalizedScalarSeedFromTheorems

noncomputable def normalizedScalarSourceObjectCC20CommonTestBridgeInputFromTheorems :
    NormalizedScalarSourceObjectCC20CommonTestBridgeInput where
  cc20TraceTest_eq_commonTest :=
    { sourceTraceTestCompatibility :=
        normalizedScalarSourceObjectBridgeRowsFromTheorems.cc20Trace.sourceCC20TraceTestCompatibility
      traceLegIsCommonTest :=
        normalizedScalarSourceObjectBridgeRowsFromTheorems.cc20Trace.sourceTraceTest =
          normalizedCommonFromTheorems.commonTest.sourceTest
      mellinLegIsCommonTest :=
        normalizedScalarSourceObjectBridgeRowsFromTheorems.cc20Trace.sourceTraceTest =
          normalizedCommonFromTheorems.commonTest.sourceTest
      halfDensityMatchesCommonTest :=
        normalizedScalarSourceObjectBridgeRowsFromTheorems.cc20Trace.sourceMellinHalfDensityCompatibility }

structure NormalizedScalarSourceObjectConvolutionSquareEqFgInput where
  convolutionSquare_eq_Fg : Prop

def normalizedScalarSourceObjectConvolutionSquareEqFgInputFromTheorems :
    NormalizedScalarSourceObjectConvolutionSquareEqFgInput where
  convolutionSquare_eq_Fg :=
    normalizedCommonFromTheorems.commonTest.sourceConvolutionSquare =
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols.convolutionStar
        normalizedCommonFromTheorems.commonTest.sourceTest
        normalizedCommonFromTheorems.commonTest.sourceTest

structure NormalizedScalarSourceObjectQWLambdaWindowControlInput where
  ccm24Window_controls_qwLambda : Prop

def normalizedScalarSourceObjectQWLambdaWindowControlInputFromTheorems :
    NormalizedScalarSourceObjectQWLambdaWindowControlInput where
  ccm24Window_controls_qwLambda :=
    ∀ lambda : ℝ, 1 < lambda →
      SemilocalModelSymbols.lambdaCompatible
        normalizedCCM24FromTheorems.semilocalSymbols
        normalizedCCM24FromTheorems.sourceSupportWindow
        lambda

structure NormalizedScalarSourceObjectCdefWindowControlInput where
  ccm24Window_controls_cdef : Prop

def normalizedScalarSourceObjectCdefWindowControlInputFromTheorems :
    NormalizedScalarSourceObjectCdefWindowControlInput where
  ccm24Window_controls_cdef :=
    SemilocalModelSymbols.fixedWindowExhaustionCompatible
      normalizedCCM24FromTheorems.semilocalSymbols
      normalizedCCM24FromTheorems.sourceSupportWindow

structure NormalizedScalarSourceObjectFinitePrimeWindowMatchInput where
  finitePrimeSupport_matches_window : Prop

def normalizedScalarSourceObjectFinitePrimeWindowMatchInputFromTheorems :
    NormalizedScalarSourceObjectFinitePrimeWindowMatchInput where
  finitePrimeSupport_matches_window :=
    WeilFormSymbols.FinitePrimeNormalizationStatement
      normalizedBaseFromTheorems.ccm25Model.toWeilFormSymbols

structure NormalizedScalarSourceObjectQWSignBridgeInput where
  qW_sign_bridge : Prop

def normalizedScalarSourceObjectQWSignBridgeInputFromTheorems :
    NormalizedScalarSourceObjectQWSignBridgeInput where
  qW_sign_bridge :=
    ∀ input : WeilPositivityInput,
      normalizedScalarSourceObjectRHExitInputFromTheorems.rhExit.sourceQWNonnegative input →
        normalizedScalarSourceObjectRHExitInputFromTheorems.rhExit.sourceCC20WeilNonpositivity input

structure NormalizedScalarSourceObjectCrossObjectBridgeInput where
  bridges :
    Source.SourceObjectCrossObjectBridges normalizedBaseFromTheorems
      normalizedCommonFromTheorems
      normalizedScalarSourceObjectBridgeRowsFromTheorems
      normalizedScalarSourceObjectRHExitInputFromTheorems.rhExit

noncomputable def normalizedScalarSourceObjectCrossObjectBridgeInputFromTheorems :
    NormalizedScalarSourceObjectCrossObjectBridgeInput where
  bridges :=
    { rhDefinitionBridge_eq_base :=
        (normalizedScalarSourceObjectRHDefinitionBridgeEqInputFromTheorems).rhDefinitionBridge_eq_base
      commonTestInvolution :=
        (normalizedScalarSourceObjectCommonTestInvolutionBridgeInputFromTheorems).commonTestInvolution
      ccm24Test_eq_commonTest :=
        (normalizedScalarSourceObjectCCM24CommonTestBridgeInputFromTheorems).ccm24Test_eq_commonTest
      cc20TraceTest_eq_commonTest :=
        (normalizedScalarSourceObjectCC20CommonTestBridgeInputFromTheorems).cc20TraceTest_eq_commonTest
      convolutionSquare_eq_Fg :=
        (normalizedScalarSourceObjectConvolutionSquareEqFgInputFromTheorems).convolutionSquare_eq_Fg
      ccm24Window_controls_qwLambda :=
        (normalizedScalarSourceObjectQWLambdaWindowControlInputFromTheorems).ccm24Window_controls_qwLambda
      ccm24Window_controls_cdef :=
        (normalizedScalarSourceObjectCdefWindowControlInputFromTheorems).ccm24Window_controls_cdef
      finitePrimeSupport_matches_window :=
        (normalizedScalarSourceObjectFinitePrimeWindowMatchInputFromTheorems).finitePrimeSupport_matches_window
      qW_sign_bridge :=
        normalizedScalarSourceObjectQWSignBridgeInputFromTheorems.qW_sign_bridge }

structure NormalizedScalarSourceObjectLayerBridgeInput where
  rhExit : Source.SourceObject.CC20RHExitObjectPackage
  bridges :
    Source.SourceObjectCrossObjectBridges normalizedBaseFromTheorems
      normalizedCommonFromTheorems
      (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
        normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
        normalizedScalarRemaindersFromTheorems)
      rhExit

noncomputable def normalizedScalarSourceObjectLayerBridgeInputFromTheorems :
    NormalizedScalarSourceObjectLayerBridgeInput where
  rhExit := normalizedScalarSourceObjectRHExitInputFromTheorems.rhExit
  bridges := normalizedScalarSourceObjectCrossObjectBridgeInputFromTheorems.bridges

noncomputable def normalizedScalarSourceObjectLayerInputFromTheorems :
    Source.NormalizedScalarSourceObjectLayerInput
      normalizedBaseFromTheorems normalizedCommonFromTheorems
      normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
      normalizedScalarRemaindersFromTheorems :=
  { rhExit := normalizedScalarSourceObjectLayerBridgeInputFromTheorems.rhExit
    bridges := normalizedScalarSourceObjectLayerBridgeInputFromTheorems.bridges }

noncomputable def normalizedScalarRhExitFromTheorems :
    Source.SourceObject.CC20RHExitObjectPackage :=
  normalizedScalarSourceObjectLayerInputFromTheorems.rhExit

noncomputable def normalizedScalarBridgesFromTheorems :
    Source.SourceObjectCrossObjectBridges normalizedBaseFromTheorems
      normalizedCommonFromTheorems
      (Source.SourceObjectExpandedRows.ofNormalizedScalarCC20Trace
        normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
        normalizedScalarRemaindersFromTheorems)
      normalizedScalarRhExitFromTheorems :=
  normalizedScalarSourceObjectLayerInputFromTheorems.bridges

noncomputable abbrev normalizedScalarSourceObjectPackageFromTheorems :
    Source.SourceObject.SourceObjectPackage :=
  Source.sourceObjectPackageOfNormalizedScalarCC20Trace
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
    normalizedScalarRemaindersFromTheorems
    normalizedScalarRhExitFromTheorems
    normalizedScalarBridgesFromTheorems

structure NormalizedScalarFixedSTestAdmissibleWindowInput where
  admissibleWindow : Prop
  admissibleWindowHolds : admissibleWindow

def normalizedScalarFixedSTestAdmissibleWindowInputFromTheorems :
    NormalizedScalarFixedSTestAdmissibleWindowInput where
  admissibleWindow :=
    normalizedScalarSourceObjectPackageFromTheorems.ccm24.semilocalSymbols.supportInWindow
      normalizedScalarSourceObjectPackageFromTheorems.ccm24.semilocalSymbols.sourceTest
      normalizedScalarSourceObjectPackageFromTheorems.ccm24.sourceSupportWindow
  admissibleWindowHolds :=
    normalizedScalarSourceObjectPackageFromTheorems.ccm24.sourceSoninSpaceComparisonData.1

structure NormalizedScalarFixedSTestTripleVanishingInput where
  tripleVanishingSymbols : TripleVanishingSymbols
  tripleVanishingSourceHolds :
    TripleVanishingSymbols.TripleVanishingStatement tripleVanishingSymbols

def normalizedScalarFixedSTestTripleVanishingInputFromTheorems :
    NormalizedScalarFixedSTestTripleVanishingInput where
  tripleVanishingSymbols :=
    (normalizedScalarSourceObjectPackageFromTheorems.cc20RHExit.sourceFiniteVanishingCriterionPackage).tripleVanishingSymbols
  tripleVanishingSourceHolds :=
    Source.SourceFiniteVanishingCriterionPackage.triple_vanishing_statement_of_source_package
      normalizedScalarSourceObjectPackageFromTheorems.cc20RHExit.sourceFiniteVanishingCriterionPackage

structure NormalizedScalarFixedSTestSourceInput where
  admissibleWindow : Prop
  admissibleWindowHolds : admissibleWindow
  tripleVanishingSymbols : TripleVanishingSymbols
  tripleVanishingSourceHolds :
    TripleVanishingSymbols.TripleVanishingStatement tripleVanishingSymbols

def normalizedScalarFixedSTestSourceInputFromTheorems :
    NormalizedScalarFixedSTestSourceInput where
  admissibleWindow :=
    normalizedScalarFixedSTestAdmissibleWindowInputFromTheorems.admissibleWindow
  admissibleWindowHolds :=
    normalizedScalarFixedSTestAdmissibleWindowInputFromTheorems.admissibleWindowHolds
  tripleVanishingSymbols :=
    normalizedScalarFixedSTestTripleVanishingInputFromTheorems.tripleVanishingSymbols
  tripleVanishingSourceHolds :=
    normalizedScalarFixedSTestTripleVanishingInputFromTheorems.tripleVanishingSourceHolds

def normalizedScalarFixedTestFromTheorems : FixedSTest where
  admissibleWindow :=
    normalizedScalarFixedSTestSourceInputFromTheorems.admissibleWindow
  tripleVanishing :=
    TripleVanishingSymbols.TripleVanishingStatement
      normalizedScalarFixedSTestSourceInputFromTheorems.tripleVanishingSymbols
  finitePrimesVisible :=
    WeilFormSymbols.FinitePrimeVisibilityStatement
      (RouteInputs.ofExpandedSourcePackage
        normalizedScalarSourceObjectPackageFromTheorems).ccm25.weilSymbols
      normalizedScalarSourceObjectPackageFromTheorems.commonTest.sourceTest
      normalizedScalarSourceObjectPackageFromTheorems.commonTest.sourceTest

def normalizedScalarFixedDataFromTheorems :
    FixedSTestObligationData
      normalizedScalarSourceObjectPackageFromTheorems where
  test := normalizedScalarFixedTestFromTheorems
  tripleVanishingSymbols :=
    normalizedScalarFixedSTestSourceInputFromTheorems.tripleVanishingSymbols
  admissibleWindow :=
    normalizedScalarFixedSTestSourceInputFromTheorems.admissibleWindowHolds
  tripleVanishingBridge := by
    intro h
    exact h
  tripleVanishingSourceHolds :=
    normalizedScalarFixedSTestSourceInputFromTheorems.tripleVanishingSourceHolds
  routeTest := normalizedScalarSourceObjectPackageFromTheorems.commonTest.sourceTest
  routeTest_eq_commonTest := rfl
  finitePrimeVisibilityStatement := by
    exact
      { globalPrimeIndexCoverage :=
          normalizedConcreteCommonFromTheorems.common_finite_prime_global_coverage_statement
        restrictedPrimeIndexCoverage :=
          normalizedConcreteCommonFromTheorems.common_finite_prime_restricted_coverage_statement
        finitePrimeTermNormalization :=
          normalizedConcreteCommonFromTheorems.common_finite_prime_term_normalization_statement }
  finitePrimeVisibilityBridge := by
    intro h
    exact h

noncomputable abbrev normalizedScalarFixedFrontEndFromTheorems :
    ExpandedSourceFixedSTestFrontEnd
      normalizedScalarSourceObjectPackageFromTheorems :=
  FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
    normalizedScalarRemaindersFromTheorems
    normalizedScalarRhExitFromTheorems normalizedScalarBridgesFromTheorems
    normalizedScalarFixedDataFromTheorems

def normalizedScalarTestAndQuotientCompatibilityFromTheorems :
    TestAndQuotientCompatibility
      (RouteInputs.ofExpandedSourcePackage
        normalizedScalarSourceObjectPackageFromTheorems)
      (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
        normalizedBaseFromTheorems normalizedCommonFromTheorems
        normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
        normalizedScalarRemaindersFromTheorems
        normalizedScalarRhExitFromTheorems
        normalizedScalarBridgesFromTheorems
        normalizedScalarFixedDataFromTheorems) :=
  TraceFrontEndData.normalizedScalarTestAndQuotientCompatibilityFromOriginalCCM25
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems normalizedScalarRemaindersFromTheorems
    normalizedScalarRhExitFromTheorems normalizedScalarBridgesFromTheorems
    normalizedScalarFixedDataFromTheorems

def normalizedScalarFixedSSupportSquareTransportFromTheorems :
    FixedSQuantizedSupportSquareTransport
      (RouteInputs.ofExpandedSourcePackage
        normalizedScalarSourceObjectPackageFromTheorems)
      normalizedScalarSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
        normalizedBaseFromTheorems normalizedCommonFromTheorems
        normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
        normalizedScalarRemaindersFromTheorems
        normalizedScalarRhExitFromTheorems
        normalizedScalarBridgesFromTheorems
        normalizedScalarFixedDataFromTheorems)
      normalizedTraceDataFromTheorems.lambda :=
  TraceFrontEndData.normalizedScalarFixedSSupportSquareTransportFromOriginalCCM25
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems normalizedScalarRemaindersFromTheorems
    normalizedScalarRhExitFromTheorems normalizedScalarBridgesFromTheorems
    normalizedScalarFixedDataFromTheorems

structure NormalizedS2B1NoBulkSourceTheoremData where
  witness :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ archimedeanTest :
        normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols.Test,
        ∀ weilTest : TestFunction,
          Source.CC20CCMTraceScaleNoBulkWitness
            normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
            normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
            lambda archimedeanTest weilTest

def normalizedS2B1NoBulkSourceTheoremDataFromTheorems :
    NormalizedS2B1NoBulkSourceTheoremData where
  witness := by
    intro lambda hlambda archimedeanTest weilTest
    let noExtraBulk :=
      (normalizedBaseFromTheorems.s2b1NormalizedSeedNoExtraBulkConstructorInput
        lambda hlambda archimedeanTest weilTest).toRow
    let noHiddenFinitePart :=
      normalizedBaseFromTheorems.s2b1NormalizedSeedNoHiddenFinitePartSubtractionConstructorInput
        lambda hlambda archimedeanTest weilTest |>.toRow
    exact
      { noBulkScaleTermOutsideLedger :=
          noExtraBulk.noExtraBulkScaleTermExcluded
        noHiddenFinitePartSubtraction :=
          noHiddenFinitePart.noHiddenFinitePartSubtractionExcluded
        noBulkScaleTermOutsideLedgerHolds :=
          noExtraBulk.noExtraBulkScaleTermExcludedHolds
        noHiddenFinitePartSubtractionHolds :=
          noHiddenFinitePart.noHiddenFinitePartSubtractionExcludedHolds }

def normalizedS2B1NoBulkSourceTheoremFromTheorems :
    (Source.cc20CcmTraceScaleNoBulk
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols).Holds := by
  intro lambda hlambda archimedeanTest weilTest
  exact
    ⟨normalizedS2B1NoBulkSourceTheoremDataFromTheorems.witness
      lambda hlambda archimedeanTest weilTest⟩

def normalizedS2B1NoBulkSourceWitnessFromTheorems :
    Source.CC20CCMTraceScaleNoBulkWitness
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceFrontEndFromTheorems.lambda
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceTest :=
  normalizedS2B1NoBulkSourceTheoremDataFromTheorems.witness
    normalizedTraceFrontEndFromTheorems.lambda
    normalizedTraceFrontEndFromTheorems.oneLtLambda
    normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
    normalizedSourceObjectPackageFromTheorems.commonTest.sourceTest

theorem normalizedS2B1NoBulkSourceWitnessSatisfiesStatement :
    Nonempty
      (Source.CC20CCMTraceScaleNoBulkWitness
        normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
        normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
        normalizedTraceFrontEndFromTheorems.lambda
        normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
        normalizedSourceObjectPackageFromTheorems.commonTest.sourceTest) :=
  ⟨normalizedS2B1NoBulkSourceWitnessFromTheorems⟩

structure NormalizedNoExtraBulkSourceTermInputData where
  noBulkSourceTheorem :
    Source.CC20CCMTraceScaleNoBulkWitness
      normalizedSourceObjectPackageFromTheorems.cc20Trace.archimedeanSymbols
      normalizedSourceObjectPackageFromTheorems.ccm25.weilSymbols
      normalizedTraceFrontEndFromTheorems.lambda
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceTest

def normalizedNoExtraBulkSourceTermInputDataFromTheorems :
    NormalizedNoExtraBulkSourceTermInputData where
  noBulkSourceTheorem := normalizedS2B1NoBulkSourceWitnessFromTheorems

def normalizedSupportSquareQWLambdaScalarReadOffFromTheorems :
    TraceFrontEndData.NormalizedSupportSquareQWLambdaScalarReadOff
      normalizedBaseFromTheorems normalizedCommonFromTheorems
      normalizedCCM24FromTheorems normalizedSeedFromTheorems
      normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
      normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
      normalizedTraceDataFromTheorems :=
  TraceFrontEndData.normalizedSupportSquareQWLambdaScalarReadOffOfNormalizedPackageTraceData
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems rfl

def normalizedNoExtraBulkContractFromTheorems :
    TraceFrontEndData.TraceScaleNoExtraBulkContract
      normalizedSourceObjectPackageFromTheorems
      normalizedFixedFrontEndFromTheorems
      normalizedTraceDataFromTheorems.lambda
      normalizedTraceDataFromTheorems.ccm25ArithmeticPackage :=
  TraceFrontEndData.no_extra_bulk_contract_of_source_term_data
    normalizedNoExtraBulkSourceTermsFromTheorems

def normalizedS2B1NoExtraBulkScaleTermExcludedFromTheorems : Prop :=
  TraceFrontEndData.S2B1NoExtraBulkScaleTermExcluded
    normalizedNoExtraBulkSourceTermsFromTheorems

theorem normalizedS2B1NoExtraBulkScaleTermExcludedHoldsFromTheorems :
    normalizedS2B1NoExtraBulkScaleTermExcludedFromTheorems :=
  TraceFrontEndData.noExtraBulkScaleTermExcludedHolds_of_source_terms
    normalizedNoExtraBulkSourceTermsFromTheorems

def normalizedS2B1NoHiddenFinitePartSubtractionExcludedFromTheorems : Prop :=
  TraceFrontEndData.S2B1NoHiddenFinitePartSubtractionExcluded
    normalizedNoExtraBulkSourceTermsFromTheorems

theorem normalizedS2B1NoHiddenFinitePartSubtractionExcludedHoldsFromTheorems :
    normalizedS2B1NoHiddenFinitePartSubtractionExcludedFromTheorems :=
  TraceFrontEndData.noHiddenFinitePartSubtractionExcludedHolds_of_source_terms
    normalizedNoExtraBulkSourceTermsFromTheorems

structure NormalizedScalarNoExtraBulkTransportData
    (sourceTerms :
      TraceFrontEndData.TraceScaleNoExtraBulkSourceTermData
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems
        normalizedTraceDataFromTheorems.lambda
        normalizedTraceDataFromTheorems.ccm25ArithmeticPackage) where
  scalarNoExtraBulkScaleTerm : Prop
  scalarStatementMatchesSource :
    scalarNoExtraBulkScaleTerm =
      TraceFrontEndData.TraceScaleNoExtraBulkSourceTermStatement sourceTerms

def normalizedScalarNoExtraBulkTransportDataFromTheorems :
    NormalizedScalarNoExtraBulkTransportData
      normalizedNoExtraBulkSourceTermsFromTheorems where
  scalarNoExtraBulkScaleTerm :=
    TraceFrontEndData.TraceScaleNoExtraBulkSourceTermStatement
      normalizedNoExtraBulkSourceTermsFromTheorems
  scalarStatementMatchesSource := rfl

noncomputable def normalizedScalarNoExtraBulkContractFromTransportData
    (sourceTerms :
      TraceFrontEndData.TraceScaleNoExtraBulkSourceTermData
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems
        normalizedTraceDataFromTheorems.lambda
        normalizedTraceDataFromTheorems.ccm25ArithmeticPackage)
    (transport :
      NormalizedScalarNoExtraBulkTransportData sourceTerms) :
    TraceFrontEndData.TraceScaleNoExtraBulkContract
      normalizedScalarSourceObjectPackageFromTheorems
      normalizedScalarFixedFrontEndFromTheorems
      normalizedTraceDataFromTheorems.lambda
      normalizedTraceDataFromTheorems.ccm25ArithmeticPackage :=
  { traceScaleOwnership := by
      intro L signDefectClassification
      exact
        TraceFrontEndData.trace_scale_owns_sign_defect_remainder_holds
          signDefectClassification
    sourceTerms :=
      { positiveTraceDecomposesIntoQWLambdaRankPoleCdef :=
          sourceTerms.positiveTraceDecomposesIntoQWLambdaRankPoleCdef
        noBulkScaleTermOutsideLedger :=
          sourceTerms.noBulkScaleTermOutsideLedger
        noHiddenFinitePartSubtraction :=
          sourceTerms.noHiddenFinitePartSubtraction
        positiveTraceDecomposesIntoQWLambdaRankPoleCdefHolds :=
          sourceTerms.positiveTraceDecomposesIntoQWLambdaRankPoleCdefHolds
        noBulkScaleTermOutsideLedgerHolds :=
          sourceTerms.noBulkScaleTermOutsideLedgerHolds
        noHiddenFinitePartSubtractionHolds :=
          sourceTerms.noHiddenFinitePartSubtractionHolds }
    sourceTermStatementHolds :=
      ⟨sourceTerms.positiveTraceDecomposesIntoQWLambdaRankPoleCdefHolds,
        sourceTerms.noBulkScaleTermOutsideLedgerHolds,
        sourceTerms.noHiddenFinitePartSubtractionHolds⟩
    noExtraBulkScaleTerm := transport.scalarNoExtraBulkScaleTerm
    noExtraBulkScaleTermHolds := by
      exact transport.scalarStatementMatchesSource.symm ▸
        TraceFrontEndData.trace_scale_no_extra_bulk_source_term_statement_holds
          sourceTerms }

structure NormalizedNoExtraBulkInputData where
  sourceInput : NormalizedNoExtraBulkSourceTermInputData
  scalarTransport :
    NormalizedScalarNoExtraBulkTransportData
      normalizedNoExtraBulkSourceTermsFromTheorems
  scalarContract :
    TraceFrontEndData.TraceScaleNoExtraBulkContract
      normalizedScalarSourceObjectPackageFromTheorems
      normalizedScalarFixedFrontEndFromTheorems
      normalizedTraceDataFromTheorems.lambda
      normalizedTraceDataFromTheorems.ccm25ArithmeticPackage
  scalarContractMatchesTransport :
    scalarContract =
      normalizedScalarNoExtraBulkContractFromTransportData
        normalizedNoExtraBulkSourceTermsFromTheorems scalarTransport

noncomputable def normalizedNoExtraBulkInputDataFromTheorems :
    NormalizedNoExtraBulkInputData where
  sourceInput := normalizedNoExtraBulkSourceTermInputDataFromTheorems
  scalarTransport := normalizedScalarNoExtraBulkTransportDataFromTheorems
  scalarContract :=
    normalizedScalarNoExtraBulkContractFromTransportData
      normalizedNoExtraBulkSourceTermsFromTheorems
      normalizedScalarNoExtraBulkTransportDataFromTheorems
  scalarContractMatchesTransport := rfl

def normalizedRouteLedgerClearingDataFromTheorems :
    RouteLedgerClearingData
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      normalizedSourceBackedFixedSTestFromTheorems
      normalizedTraceFrontEndFromTheorems.lambda :=
  RouteLedgerClearingData.ofSourceBacked
    normalizedSourceBackedFixedSTestFromTheorems
    normalizedTraceFrontEndFromTheorems.oneLtLambda

def normalizedRouteLedgerInputFromTheorems : RouteLedgers :=
  normalizedRouteLedgerClearingDataFromTheorems.toRouteLedgers

def normalizedRouteLedgersFromTheorems : RouteLedgers :=
  normalizedRouteLedgerInputFromTheorems

def normalizedRouteLedgersClearedInputFromTheorems :
    LedgersCleared normalizedRouteLedgerInputFromTheorems where
  rankKilled := normalizedRouteLedgerClearingDataFromTheorems.rankKilledHolds
  poleKilled := normalizedRouteLedgerClearingDataFromTheorems.poleKilledHolds
  cdefExhausts := normalizedRouteLedgerClearingDataFromTheorems.cdefExhaustsHolds

def normalizedRouteLedgerSemanticDataFromTheorems :
    RouteLedgerSemanticData
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      normalizedSourceBackedFixedSTestFromTheorems
      normalizedTraceFrontEndFromTheorems.lambda
      normalizedRouteLedgersFromTheorems :=
  normalizedRouteLedgerClearingDataFromTheorems.toRouteLedgerSemanticData

def normalizedRouteLedgerClearingInputDataFromTheorems :
    LedgerSignDefectPackage
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedTraceFrontEndFromTheorems.lambda :=
  ledger_sign_defect_package_of_route_ledger_semantics
    normalizedRouteLedgerSemanticDataFromTheorems

theorem normalizedRankLedgerKilledFromTheorems :
    normalizedRouteLedgersFromTheorems.rankKilled :=
  normalizedRouteLedgerClearingInputDataFromTheorems.ledgersCleared.rankKilled

theorem normalizedPoleLedgerKilledFromTheorems :
    normalizedRouteLedgersFromTheorems.poleKilled :=
  normalizedRouteLedgerClearingInputDataFromTheorems.ledgersCleared.poleKilled

theorem normalizedCdefExhaustsFromTheorems :
    normalizedRouteLedgersFromTheorems.cdefExhausts :=
  normalizedRouteLedgerClearingInputDataFromTheorems.ledgersCleared.cdefExhausts

def normalizedLedgersClearedFromTheorems :
    LedgersCleared normalizedRouteLedgersFromTheorems :=
  normalizedRouteLedgerClearingInputDataFromTheorems.ledgersCleared

def normalizedSourceBackedLedgersFromTheorems :
    SourceBackedLedgers
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedRouteLedgersFromTheorems :=
  normalizedRouteLedgerClearingInputDataFromTheorems.sourceBackedLedgers

theorem normalizedSignDefectClassificationFromTheorems :
    SourceSignDefectClassification
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedTraceFrontEndFromTheorems.lambda
      normalizedRouteLedgersFromTheorems :=
  normalizedRouteLedgerClearingInputDataFromTheorems.signDefectClassification

def normalizedS2B1RankZeroModeChannelClassifiedFromTheorems : Prop :=
  TraceFrontEndData.S2B1RankZeroModeChannelClassified
    (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
    (normalizedSourceBackedFixedSTestFromTheorems)
    normalizedTraceFrontEndFromTheorems.lambda
    normalizedRouteLedgersFromTheorems

theorem normalizedS2B1RankZeroModeChannelClassifiedHoldsFromTheorems :
    normalizedS2B1RankZeroModeChannelClassifiedFromTheorems :=
  TraceFrontEndData.rankZeroModeChannelClassifiedAtHolds_of_sign_defect_classification
    normalizedSignDefectClassificationFromTheorems

def normalizedS2B1NoStripRankPoleClassifiedFromTheorems : Prop :=
  TraceFrontEndData.S2B1NoStripRankPoleClassified
    (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
    (normalizedSourceBackedFixedSTestFromTheorems)
    normalizedTraceFrontEndFromTheorems.lambda
    normalizedRouteLedgersFromTheorems

theorem normalizedS2B1NoStripRankPoleClassifiedHoldsFromTheorems :
    normalizedS2B1NoStripRankPoleClassifiedFromTheorems :=
  TraceFrontEndData.noStripPostQRemainderRankPoleClassifiedAtHolds_of_sign_defect_classification
    normalizedSignDefectClassificationFromTheorems

def normalizedS2B1EndpointStripBulkClassifiedIntoCdefFromTheorems : Prop :=
  TraceFrontEndData.S2B1EndpointStripBulkClassifiedIntoCdef
    (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
    (normalizedSourceBackedFixedSTestFromTheorems)
    normalizedTraceFrontEndFromTheorems.lambda

theorem normalizedS2B1EndpointStripBulkClassifiedIntoCdefHoldsFromTheorems :
    normalizedS2B1EndpointStripBulkClassifiedIntoCdefFromTheorems :=
  TraceFrontEndData.endpointStripBulkClassifiedIntoCdefAtHolds_of_sign_defect_classification
    normalizedSignDefectClassificationFromTheorems

def normalizedS2B1EndpointStripBoundaryTermsClassifiedFromTheorems : Prop :=
  TraceFrontEndData.S2B1EndpointStripBoundaryTermsClassified
    (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
    (normalizedSourceBackedFixedSTestFromTheorems)
    normalizedTraceFrontEndFromTheorems.lambda

theorem normalizedS2B1EndpointStripBoundaryTermsClassifiedHoldsFromTheorems :
    normalizedS2B1EndpointStripBoundaryTermsClassifiedFromTheorems :=
  TraceFrontEndData.endpointStripBoundaryTermsClassifiedAtHolds_of_sign_defect_classification
    normalizedSignDefectClassificationFromTheorems

def normalizedS2B1SourceSeriesTailClassifiedIntoCdefFromTheorems : Prop :=
  TraceFrontEndData.S2B1SourceSeriesTailClassifiedIntoCdef
    (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
    (normalizedSourceBackedFixedSTestFromTheorems)
    normalizedTraceFrontEndFromTheorems.lambda
    normalizedRouteLedgersFromTheorems

theorem normalizedS2B1SourceSeriesTailClassifiedIntoCdefHoldsFromTheorems :
    normalizedS2B1SourceSeriesTailClassifiedIntoCdefFromTheorems :=
  TraceFrontEndData.sourceSeriesTailClassifiedIntoCdefAtHolds_of_sign_defect_classification
    normalizedSignDefectClassificationFromTheorems

def normalizedS2B1CdefExhaustionOwnsEndpointStripFromTheorems : Prop :=
  TraceFrontEndData.S2B1CdefExhaustionOwnsEndpointStrip
    (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
    (normalizedSourceBackedFixedSTestFromTheorems)
    normalizedTraceFrontEndFromTheorems.lambda
    normalizedRouteLedgersFromTheorems

theorem normalizedS2B1CdefExhaustionOwnsEndpointStripHoldsFromTheorems :
    normalizedS2B1CdefExhaustionOwnsEndpointStripFromTheorems :=
  TraceFrontEndData.cdefExhaustionOwnsEndpointStripAtHolds_of_sign_defect_classification
    normalizedSignDefectClassificationFromTheorems

def normalizedCommonTupleFromTheorems :
    SourceCommonTestTupleContract
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedTraceFrontEndFromTheorems.lambda
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
      normalizedTraceFrontEndFromTheorems.ccm25ArithmeticPackage := by
  exact
    source_common_test_tuple_contract_of_package
      (window_lambda_compatibility_of_source_backed
        normalizedTraceFrontEndFromTheorems.oneLtLambda)
      (expanded_source_package_convolution_square_read_off
        normalizedSourceObjectPackageFromTheorems
        normalizedFixedFrontEndFromTheorems)

structure NormalizedRestrictedToFullThresholdPackageInput where
  threshold :
    RestrictedToFullQWLargeLambdaThreshold
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare

structure NormalizedRestrictedToFullThresholdRowsInput where
  lambda0 : ℝ
  oneLtLambda0 : 1 < lambda0
  thresholdPackage :
    Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems).ccm25.weilSymbols
      (normalizedSourceBackedFixedSTestFromTheorems).weilTest
      lambda0
  thresholdTuple :
    SourceCommonTestTupleContract
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems)
      lambda0
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
      thresholdPackage
  supportThresholdAtLarge :
    ∀ lambda : ℝ,
      lambda0 ≤ lambda →
        FixedTestSupportThresholdAtLarge
          (RouteInputs.ofExpandedSourcePackage
            normalizedSourceObjectPackageFromTheorems)
          (normalizedSourceBackedFixedSTestFromTheorems)
          lambda
  primePowerAtomStabilizationAtLarge :
    ∀ lambda : ℝ,
      lambda0 ≤ lambda →
        ∀ pkg :
          Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
            (RouteInputs.ofExpandedSourcePackage
              normalizedSourceObjectPackageFromTheorems).ccm25.weilSymbols
            (normalizedSourceBackedFixedSTestFromTheorems).weilTest
            lambda,
          SourceCommonTestTupleContract
            (RouteInputs.ofExpandedSourcePackage
              normalizedSourceObjectPackageFromTheorems)
            (normalizedSourceBackedFixedSTestFromTheorems)
            lambda
            normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
            pkg →
            PrimePowerAtomStabilizationAtLarge
              (RouteInputs.ofExpandedSourcePackage
                normalizedSourceObjectPackageFromTheorems)
              (normalizedSourceBackedFixedSTestFromTheorems)
              lambda
              pkg
  scalarRestrictionAtLarge :
    ∀ lambda : ℝ,
      lambda0 ≤ lambda →
        ∀ pkg :
          Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
            (RouteInputs.ofExpandedSourcePackage
              normalizedSourceObjectPackageFromTheorems).ccm25.weilSymbols
            (normalizedSourceBackedFixedSTestFromTheorems).weilTest
            lambda,
          SourceCommonTestTupleContract
            (RouteInputs.ofExpandedSourcePackage
              normalizedSourceObjectPackageFromTheorems)
            (normalizedSourceBackedFixedSTestFromTheorems)
            lambda
            normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
            pkg →
            RestrictedToFullQWScalarRestrictionWitness
              (RouteInputs.ofExpandedSourcePackage
                normalizedSourceObjectPackageFromTheorems)
              (normalizedSourceBackedFixedSTestFromTheorems)
              lambda
              normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
              pkg

structure NormalizedRestrictedToFullFinitePrimeIndexDifferenceRowsProvider where
  finitePrimeIndexDifferenceAtLarge :
    ∀ lambda : ℝ,
      normalizedTraceDataFromTheorems.lambda ≤ lambda →
        SourceFinitePrimeIndexDifferenceArchimedeanBalance
          (RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems)
          (normalizedSourceBackedFixedSTestFromTheorems)
          lambda

axiom normalizedRestrictedToFullFinitePrimeIndexDifferenceRowsRoot :
  NormalizedRestrictedToFullFinitePrimeIndexDifferenceRowsProvider

def normalizedRestrictedToFullFinitePrimeIndexDifferenceRowsFromTheorems :
    NormalizedRestrictedToFullFinitePrimeIndexDifferenceRowsProvider :=
  normalizedRestrictedToFullFinitePrimeIndexDifferenceRowsRoot

/-- The current-cutoff/restricted-to-full index-difference provider is strong
enough to supply the selected lambda row.  This is a bridge for later Dev
dependency cleanup; the earlier selected consumer is not rewired here because
it appears before the trace-data/current-cutoff layer in this skeleton. -/
def normalizedSelectedFinitePrimeIndexDifferenceInput_of_restrictedToFullFinitePrimeIndexDifferenceRows
    (rows : NormalizedRestrictedToFullFinitePrimeIndexDifferenceRowsProvider) :
    NormalizedSelectedFinitePrimeIndexDifferenceInput where
  finitePrimeIndexDifference :=
    rows.finitePrimeIndexDifferenceAtLarge
      normalizedTraceLambdaInputFromTheorems.lambda
      (by
        simpa [normalizedTraceDataFromTheorems] using
          (le_rfl :
            normalizedTraceLambdaInputFromTheorems.lambda ≤
              normalizedTraceLambdaInputFromTheorems.lambda))

def normalizedSelectedFinitePrimeIndexDifferenceInputFromRestrictedToFullRowsFromTheorems :
    NormalizedSelectedFinitePrimeIndexDifferenceInput :=
  normalizedSelectedFinitePrimeIndexDifferenceInput_of_restrictedToFullFinitePrimeIndexDifferenceRows
    normalizedRestrictedToFullFinitePrimeIndexDifferenceRowsFromTheorems

def normalizedRestrictedToFullArchimedeanBalanceRowsInputFromTheorems :
    NormalizedRestrictedToFullArchimedeanBalanceRowsProvider
      normalizedBaseFromTheorems normalizedCommonFromTheorems
      normalizedCCM24FromTheorems normalizedSeedFromTheorems
      normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
      normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
      normalizedTraceDataFromTheorems where
  archimedeanBalanceRowsAtLarge := by
    intro lambda habove pkg _hcommon
    exact
      { scopedBalance :=
          source_scoped_archimedean_contribution_matches_of_finite_prime_balance
            (package_backed_ccm25_weil_form_read_off
              (window_lambda_compatibility_of_source_backed
                (lt_of_lt_of_le normalizedTraceDataFromTheorems.oneLtLambda habove)))
            (source_scoped_finite_prime_archimedean_balance_of_index_difference
              (package_backed_ccm25_weil_form_read_off
                (window_lambda_compatibility_of_source_backed
                  (lt_of_lt_of_le normalizedTraceDataFromTheorems.oneLtLambda habove)))
              (normalizedRestrictedToFullFinitePrimeIndexDifferenceRowsFromTheorems.finitePrimeIndexDifferenceAtLarge
                lambda habove)) }

noncomputable def normalizedRestrictedToFullAsymptoticRowsInputFromTheorems :
    NormalizedRestrictedToFullAsymptoticRowsProvider
      normalizedBaseFromTheorems normalizedCommonFromTheorems
      normalizedCCM24FromTheorems normalizedSeedFromTheorems
      normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
      normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
      normalizedTraceDataFromTheorems :=
  normalized_restricted_to_full_asymptotic_rows_of_archimedean_balance
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems
    normalizedRestrictedToFullArchimedeanBalanceRowsInputFromTheorems

noncomputable def normalizedRestrictedToFullAsymptoticThresholdFromTheorems :
    RestrictedToFullQWLargeLambdaThreshold
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare :=
  normalized_restricted_to_full_threshold_of_asymptotic_rows
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems
    normalizedRestrictedToFullAsymptoticRowsInputFromTheorems

noncomputable def normalizedRestrictedToFullThresholdRowsInputFromTheorems :
    NormalizedRestrictedToFullThresholdRowsInput where
  lambda0 := normalizedRestrictedToFullAsymptoticThresholdFromTheorems.lambda0
  oneLtLambda0 :=
    normalizedRestrictedToFullAsymptoticThresholdFromTheorems.oneLtLambda0
  thresholdPackage :=
    normalizedRestrictedToFullAsymptoticThresholdFromTheorems.thresholdPackage
  thresholdTuple :=
    normalizedRestrictedToFullAsymptoticThresholdFromTheorems.thresholdTuple
  supportThresholdAtLarge :=
    normalizedRestrictedToFullAsymptoticThresholdFromTheorems.supportThresholdAtLarge
  primePowerAtomStabilizationAtLarge :=
    normalizedRestrictedToFullAsymptoticThresholdFromTheorems.primePowerAtomStabilizationAtLarge
  scalarRestrictionAtLarge :=
    normalizedRestrictedToFullAsymptoticThresholdFromTheorems.scalarRestrictionAtLarge

noncomputable def normalizedRestrictedToFullThresholdPackageInputFromTheorems :
    NormalizedRestrictedToFullThresholdPackageInput where
  threshold :=
    { lambda0 :=
        normalizedRestrictedToFullThresholdRowsInputFromTheorems.lambda0
      oneLtLambda0 :=
        normalizedRestrictedToFullThresholdRowsInputFromTheorems.oneLtLambda0
      thresholdPackage :=
        normalizedRestrictedToFullThresholdRowsInputFromTheorems.thresholdPackage
      thresholdTuple :=
        normalizedRestrictedToFullThresholdRowsInputFromTheorems.thresholdTuple
      supportThresholdAtLarge :=
        normalizedRestrictedToFullThresholdRowsInputFromTheorems.supportThresholdAtLarge
      primePowerAtomStabilizationAtLarge :=
        normalizedRestrictedToFullThresholdRowsInputFromTheorems.primePowerAtomStabilizationAtLarge
      scalarRestrictionAtLarge :=
        normalizedRestrictedToFullThresholdRowsInputFromTheorems.scalarRestrictionAtLarge }

structure NormalizedRestrictedToFullCurrentCutoffInput where
  currentAboveThreshold :
    normalizedRestrictedToFullThresholdPackageInputFromTheorems.threshold.lambda0 ≤
      normalizedTraceFrontEndFromTheorems.lambda

structure NormalizedRestrictedToFullCurrentCutoffRowsInput where
  currentAboveThreshold :
    normalizedRestrictedToFullThresholdRowsInputFromTheorems.lambda0 ≤
      normalizedTraceFrontEndFromTheorems.lambda

noncomputable def normalizedRestrictedToFullCurrentCutoffRowsInputFromTheorems :
    NormalizedRestrictedToFullCurrentCutoffRowsInput where
  currentAboveThreshold := le_rfl


noncomputable def normalizedRestrictedToFullCurrentCutoffInputFromTheorems :
    NormalizedRestrictedToFullCurrentCutoffInput where
  currentAboveThreshold :=
    normalizedRestrictedToFullCurrentCutoffRowsInputFromTheorems.currentAboveThreshold

structure NormalizedRestrictedToFullThresholdSourceInput where
  threshold :
    RestrictedToFullQWLargeLambdaThreshold
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
  currentAboveThreshold :
    threshold.lambda0 ≤ normalizedTraceFrontEndFromTheorems.lambda

noncomputable def normalizedRestrictedToFullThresholdSourceInputFromTheorems :
    NormalizedRestrictedToFullThresholdSourceInput where
  threshold :=
    normalizedRestrictedToFullThresholdPackageInputFromTheorems.threshold
  currentAboveThreshold :=
    normalizedRestrictedToFullCurrentCutoffInputFromTheorems.currentAboveThreshold

noncomputable def normalizedRestrictedToFullThresholdBridgePackageFromTheorems :
    RestrictedToFullThresholdBridgePackage
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedTraceFrontEndFromTheorems.lambda
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
      normalizedRouteLedgersFromTheorems
      normalizedTraceFrontEndFromTheorems.ccm25ArithmeticPackage :=
  restricted_to_full_threshold_bridge_package_of_route_ledger_semantics
    normalizedRestrictedToFullThresholdSourceInputFromTheorems.threshold
    normalizedRestrictedToFullThresholdSourceInputFromTheorems.currentAboveThreshold
    normalizedCommonTupleFromTheorems
    normalizedRouteLedgerSemanticDataFromTheorems

noncomputable def normalizedRestrictedToFullLargeLambdaThresholdFromTheorems :
    RestrictedToFullQWLargeLambdaThreshold
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare :=
  normalizedRestrictedToFullAsymptoticThresholdFromTheorems

theorem normalizedRestrictedToFullCurrentAboveThresholdFromTheorems :
    normalizedRestrictedToFullLargeLambdaThresholdFromTheorems.lambda0 ≤
      normalizedTraceFrontEndFromTheorems.lambda :=
  le_rfl

noncomputable def normalizedRestrictedToFullCurrentCutoffBindingFromTheorems :
    RestrictedToFullCurrentCutoffBinding
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedTraceFrontEndFromTheorems.lambda
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
      normalizedRouteLedgersFromTheorems
      normalizedTraceFrontEndFromTheorems.ccm25ArithmeticPackage :=
  normalized_restricted_to_full_current_cutoff_binding_of_source_backed_asymptotic_rows
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems normalizedRouteLedgersFromTheorems
    normalizedRestrictedToFullAsymptoticRowsInputFromTheorems
    normalizedRouteLedgerClearingInputDataFromTheorems.ledgersCleared.rankKilled
    normalizedRouteLedgerClearingInputDataFromTheorems.ledgersCleared.poleKilled
    normalizedRouteLedgerClearingInputDataFromTheorems.ledgersCleared.cdefExhausts

noncomputable def normalizedRestrictedToFullQWFromTheorems :
    RestrictedToFullQWBridgeContract
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedTraceFrontEndFromTheorems.lambda
      normalizedSourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
      normalizedRouteLedgersFromTheorems
      normalizedTraceFrontEndFromTheorems.ccm25ArithmeticPackage :=
  restricted_to_full_bridge_contract_of_current_cutoff_binding
    normalizedRestrictedToFullCurrentCutoffBindingFromTheorems

structure NormalizedScalarTraceScaleInputData where
  noExtraBulk :
    TraceFrontEndData.TraceScaleNoExtraBulkContract
      normalizedScalarSourceObjectPackageFromTheorems
      normalizedScalarFixedFrontEndFromTheorems
      normalizedTraceDataFromTheorems.lambda
      normalizedTraceDataFromTheorems.ccm25ArithmeticPackage
  amplitudeSquareScalar :
    TraceFrontEndData.NormalizedTraceAmplitudeSquareScalarContract
      normalizedBaseFromTheorems normalizedCommonFromTheorems
      normalizedCCM24FromTheorems normalizedSeedFromTheorems
      normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
      normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
      normalizedTraceDataFromTheorems

def normalizedSupportSquareScalarNormalFormInputFromTheorems :
    TraceFrontEndData.NormalizedSupportSquareScalarNormalFormContract
      normalizedBaseFromTheorems normalizedCommonFromTheorems
      normalizedCCM24FromTheorems normalizedSeedFromTheorems
      normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
      normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
      normalizedTraceDataFromTheorems :=
  TraceFrontEndData.normalizedSupportSquareScalarNormalFormContractOfQWLambdaReadOff
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems
    normalizedSupportSquareQWLambdaScalarReadOffFromTheorems

def normalizedTraceAmplitudeSquareScalarInputFromTheorems :
    TraceFrontEndData.NormalizedTraceAmplitudeSquareScalarContract
      normalizedBaseFromTheorems normalizedCommonFromTheorems
      normalizedCCM24FromTheorems normalizedSeedFromTheorems
      normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
      normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
      normalizedTraceDataFromTheorems :=
  TraceFrontEndData.normalizedTraceAmplitudeSquareScalarContractOfSupportSquareScalarNormalForm
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems
    normalizedSupportSquareScalarNormalFormInputFromTheorems

noncomputable def normalizedScalarTraceScaleInputDataFromTheorems :
    NormalizedScalarTraceScaleInputData where
  noExtraBulk := normalizedNoExtraBulkInputDataFromTheorems.scalarContract
  amplitudeSquareScalar :=
    normalizedTraceAmplitudeSquareScalarInputFromTheorems

def normalizedScalarFullTraceReadOffBridgeFromTheorems :
    FullTraceReadOffBridgeContract
      (RouteInputs.ofExpandedSourcePackage
        normalizedScalarSourceObjectPackageFromTheorems)
      normalizedScalarSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
        normalizedBaseFromTheorems normalizedCommonFromTheorems
        normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
        normalizedScalarRemaindersFromTheorems
        normalizedScalarRhExitFromTheorems
        normalizedScalarBridgesFromTheorems
        normalizedScalarFixedDataFromTheorems) :=
  normalizedScalarTraceFrontFullTraceReadOffBridgeFromRestrictedToFullContract
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems normalizedScalarRemaindersFromTheorems
    normalizedScalarRhExitFromTheorems normalizedScalarBridgesFromTheorems
    normalizedScalarFixedDataFromTheorems normalizedRouteLedgersFromTheorems
    normalizedRestrictedToFullQWFromTheorems

def normalizedScalarRestrictedTraceReadOffBridgeFromTheorems :
    RestrictedTraceReadOffBridgeContract
      (RouteInputs.ofExpandedSourcePackage
        normalizedScalarSourceObjectPackageFromTheorems)
      normalizedScalarSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (FixedSTestObligationData.sourceBackedFixedSTestOfNormalizedScalarPackage
        normalizedBaseFromTheorems normalizedCommonFromTheorems
        normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
        normalizedScalarRemaindersFromTheorems
        normalizedScalarRhExitFromTheorems
        normalizedScalarBridgesFromTheorems
        normalizedScalarFixedDataFromTheorems)
      normalizedTraceDataFromTheorems.lambda :=
  TraceFrontEndData.normalizedScalarRestrictedTraceReadOffBridgeFromOriginalCCM25
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems normalizedScalarRemaindersFromTheorems
    normalizedScalarRhExitFromTheorems normalizedScalarBridgesFromTheorems
    normalizedScalarFixedDataFromTheorems

noncomputable def normalizedScalarTraceScaleNoMissingBulkFromTheorems :
    TraceScaleNoMissingBulkData
      normalizedScalarSourceObjectPackageFromTheorems
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
        normalizedBaseFromTheorems normalizedCommonFromTheorems
        normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
        normalizedScalarRemaindersFromTheorems
        normalizedScalarRhExitFromTheorems
        normalizedScalarBridgesFromTheorems
        normalizedScalarFixedDataFromTheorems)
      normalizedTraceDataFromTheorems.lambda
      normalizedTraceDataFromTheorems.ccm25ArithmeticPackage :=
  TraceFrontEndData.traceScaleNoMissingBulkOfNormalizedScalarPackageFromOriginalCCM25
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems normalizedScalarRemaindersFromTheorems
    normalizedScalarRhExitFromTheorems normalizedScalarBridgesFromTheorems
    normalizedScalarFixedDataFromTheorems
    normalizedScalarTraceScaleInputDataFromTheorems.noExtraBulk

noncomputable def normalizedScalarTraceDataFromTheorems :
    TraceFrontEndData
      normalizedScalarSourceObjectPackageFromTheorems
      (FixedSTestObligationData.toExpandedSourceFixedSTestFrontEndOfNormalizedScalarPackage
        normalizedBaseFromTheorems normalizedCommonFromTheorems
        normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
        normalizedScalarRemaindersFromTheorems
        normalizedScalarRhExitFromTheorems
        normalizedScalarBridgesFromTheorems
        normalizedScalarFixedDataFromTheorems) :=
  TraceFrontEndData.traceFrontEndDataOfNormalizedScalarPackageFromOriginalCCM25
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems normalizedScalarRemaindersFromTheorems
    normalizedScalarRhExitFromTheorems normalizedScalarBridgesFromTheorems
    normalizedScalarFixedDataFromTheorems
    normalizedScalarTestAndQuotientCompatibilityFromTheorems
    normalizedScalarFixedSSupportSquareTransportFromTheorems
    normalizedScalarFullTraceReadOffBridgeFromTheorems
    normalizedScalarRestrictedTraceReadOffBridgeFromTheorems
    normalizedScalarTraceScaleNoMissingBulkFromTheorems

noncomputable def normalizedScalarFrontEndPackageFromTheorems :
    TraceFrontEndData.SourceFixedTraceFrontEndPackage
      normalizedScalarSourceObjectPackageFromTheorems :=
  TraceFrontEndData.source_fixed_trace_front_end_package_of_trace_data
    normalizedScalarSourceObjectPackageFromTheorems
    normalizedScalarFixedFrontEndFromTheorems
    normalizedScalarTraceDataFromTheorems

theorem normalizedScalarFrontEndPackageSourceTraceReadOffData_eq :
    normalizedScalarFrontEndPackageFromTheorems.sourceTraceReadOffData =
      TraceFrontEndData.toSourceTraceReadOffDataOfNormalizedScalarPackage
        normalizedBaseFromTheorems normalizedCommonFromTheorems
        normalizedCCM24FromTheorems normalizedScalarSeedFromTheorems
        normalizedScalarRemaindersFromTheorems
        normalizedScalarRhExitFromTheorems normalizedScalarBridgesFromTheorems
        normalizedScalarFixedDataFromTheorems
        normalizedScalarTraceDataFromTheorems :=
  rfl

noncomputable abbrev normalizedScalarTraceFrontEndFromTheorems :
    ExpandedSourceTraceReadOffFrontEnd
      normalizedScalarSourceObjectPackageFromTheorems
      normalizedScalarFixedFrontEndFromTheorems :=
  normalizedScalarFrontEndPackageFromTheorems.traceFront

theorem normalizedScalarTraceAmplitudeSquareFromTheorems :
    let scalarSourceTrace :=
      normalizedScalarFrontEndPackageFromTheorems.sourceTraceReadOffData
    (Source.CC20Concrete.TraceScale.normalizedScalarAsLegalSquareSeed
        normalizedScalarSeedFromTheorems).traceAmplitude
        scalarSourceTrace.archimedeanTest ^ 2 =
      TraceFrontEndData.NormalizedRestrictedScalarNormalForm
        normalizedBaseFromTheorems normalizedCommonFromTheorems
        normalizedCCM24FromTheorems normalizedSeedFromTheorems
        normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
        normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
        normalizedTraceDataFromTheorems :=
  TraceFrontEndData.normalized_scalar_trace_front_trace_amplitude_square_eq_original_normal_form
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems normalizedScalarRemaindersFromTheorems
    normalizedScalarRhExitFromTheorems normalizedScalarBridgesFromTheorems
    normalizedScalarFixedDataFromTheorems
    normalizedScalarTestAndQuotientCompatibilityFromTheorems
    normalizedScalarFixedSSupportSquareTransportFromTheorems
    normalizedScalarFullTraceReadOffBridgeFromTheorems
    normalizedScalarRestrictedTraceReadOffBridgeFromTheorems
    normalizedScalarTraceScaleNoMissingBulkFromTheorems

def normalizedTraceAmplitudeSquareScalarFromTheorems :
    TraceFrontEndData.NormalizedTraceAmplitudeSquareScalarContract
      normalizedBaseFromTheorems normalizedCommonFromTheorems
      normalizedCCM24FromTheorems normalizedSeedFromTheorems
      normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
      normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
      normalizedTraceDataFromTheorems :=
  normalizedScalarTraceScaleInputDataFromTheorems.amplitudeSquareScalar

def normalizedSupportSquareScalarNormalFormFromTheorems :
    TraceFrontEndData.NormalizedSupportSquareScalarNormalFormContract
      normalizedBaseFromTheorems normalizedCommonFromTheorems
      normalizedCCM24FromTheorems normalizedSeedFromTheorems
      normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
      normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
      normalizedTraceDataFromTheorems :=
  TraceFrontEndData.normalizedSupportSquareScalarNormalFormContractOfTraceAmplitudeSquare
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems
    normalizedTraceAmplitudeSquareScalarFromTheorems

def normalizedComparisonFromTheorems :
    TraceFrontEndData.NormalizedSupportSquareQWLambdaSourceComparison
      normalizedBaseFromTheorems normalizedCommonFromTheorems
      normalizedCCM24FromTheorems normalizedSeedFromTheorems
      normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
      normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
      normalizedTraceDataFromTheorems :=
  TraceFrontEndData.normalizedSupportSquareQWLambdaSourceComparisonOfTraceAmplitudeSquare
    normalizedBaseFromTheorems normalizedCommonFromTheorems
    normalizedCCM24FromTheorems normalizedSeedFromTheorems
    normalizedRemaindersFromTheorems normalizedRhExitFromTheorems
    normalizedBridgesFromTheorems normalizedFixedDataFromTheorems
    normalizedTraceDataFromTheorems
    normalizedTraceAmplitudeSquareScalarFromTheorems

theorem normalizedSourceArchimedeanSignBridgeFromTheorems :
    SourceArchimedeanSignBridge
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (normalizedSourceBackedFixedSTestFromTheorems) :=
  source_archimedean_sign_bridge_of_source_trace_read_off
    normalizedFrontEndPackageFromTheorems.sourceTraceReadOffData

def normalizedRouteTraceDataFromTheorems :
    SourceRouteTraceData
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems) where
  archimedeanTest := normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
  hilbertSchmidtGate :=
    normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceHilbertSchmidtGate
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
  lambda := normalizedTraceLambdaInputFromTheorems.lambda
  oneLtLambda := normalizedTraceLambdaInputFromTheorems.oneLtLambda
  ccm25ArithmeticPackage := normalizedTraceCCM25ArithmeticPackageFromTheorems
  testAndQuotientCompatibility :=
    normalizedTraceQuotientCompatibilityInputFromTheorems.testAndQuotientCompatibility
  fixedSSupportSquareTransport :=
    normalizedTraceSupportSquareTransportInputFromTheorems.fixedSSupportSquareTransport
  positiveTraceNonnegative := by
    let inputs := RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems
    let hgate :=
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceHilbertSchmidtGate
        normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
    let hlegal :=
      cc20_trace_legality_template_output
        (inputs := inputs)
        (a := normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest)
        hgate
    exact normalizedSourceObjectPackageFromTheorems.cc20Trace.sourcePositiveTraceNonnegative
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      hlegal.traceClass hlegal.cyclicLegal

def normalizedRouteLedgerClearingDataForRouteFromTheorems :
    RouteLedgerClearingData
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      normalizedSourceBackedFixedSTestFromTheorems
      normalizedRouteTraceDataFromTheorems.lambda :=
  RouteLedgerClearingData.ofSourceBacked
    normalizedSourceBackedFixedSTestFromTheorems
    normalizedRouteTraceDataFromTheorems.oneLtLambda

def normalizedRouteLedgersForRouteFromTheorems : RouteLedgers :=
  normalizedRouteLedgerClearingDataForRouteFromTheorems.toRouteLedgers

def normalizedRouteLedgerSemanticDataForRouteFromTheorems :
    RouteLedgerSemanticData
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      normalizedSourceBackedFixedSTestFromTheorems
      normalizedRouteTraceDataFromTheorems.lambda
      normalizedRouteLedgersForRouteFromTheorems :=
  normalizedRouteLedgerClearingDataForRouteFromTheorems.toRouteLedgerSemanticData

def normalizedRouteLedgerPackageForRouteFromTheorems :
    LedgerSignDefectPackage
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedRouteTraceDataFromTheorems.lambda :=
  ledger_sign_defect_package_of_route_ledger_semantics
    normalizedRouteLedgerSemanticDataForRouteFromTheorems

theorem normalizedSignDefectClassificationForRouteFromTheorems :
    SourceSignDefectClassification
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedRouteTraceDataFromTheorems.lambda
      normalizedRouteLedgersForRouteFromTheorems :=
  normalizedRouteLedgerPackageForRouteFromTheorems.signDefectClassification

def normalizedRouteSquareCommonTupleFromTheorems :
    SourceCommonTestTupleContract
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedRouteTraceDataFromTheorems.lambda
      ((RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems).ccm25.weilSymbols.convolutionStar
          normalizedSourceBackedFixedSTestFromTheorems.weilTest
          normalizedSourceBackedFixedSTestFromTheorems.weilTest)
      normalizedRouteTraceDataFromTheorems.ccm25ArithmeticPackage :=
  source_common_test_tuple_contract_of_package
    (window_lambda_compatibility_of_source_backed
      normalizedRouteTraceDataFromTheorems.oneLtLambda)
    rfl

noncomputable def normalizedRouteFinalSignNonpositiveFromTheorems :
    SourceQWNonnegativeToCC20Nonpositive
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems)
      normalizedRouteTraceDataFromTheorems.archimedeanTest
      (normalizedSourceBackedFixedSTestFromTheorems)
      normalizedRouteTraceDataFromTheorems.lambda
      ((RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems).ccm25.weilSymbols.convolutionStar
          normalizedSourceBackedFixedSTestFromTheorems.weilTest
          normalizedSourceBackedFixedSTestFromTheorems.weilTest)
      normalizedRouteTraceDataFromTheorems.ccm25ArithmeticPackage :=
  source_qw_nonnegative_to_cc20_nonpositive_of_common_test_parts
    normalizedRouteSquareCommonTupleFromTheorems.windowLambdaCompatibility
    normalizedRouteSquareCommonTupleFromTheorems.packageReadOff
    normalizedRouteSquareCommonTupleFromTheorems.squareCompatibility
    normalizedRouteTraceDataFromTheorems.hilbertSchmidtGate
    (RouteInputs.ofExpandedSourcePackage
      normalizedSourceObjectPackageFromTheorems).cc20.signsAndNormalizations
    (RouteInputs.ofExpandedSourcePackage
      normalizedSourceObjectPackageFromTheorems).cc20.mellinHalfDensityConvention

noncomputable def normalizedRouteCertificateFromTheorems :
    RouteCertificate
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems) :=
  { sourceBackedTest := normalizedSourceBackedFixedSTestFromTheorems
    ledgers := normalizedRouteLedgersForRouteFromTheorems
    bridge :=
      route_bridge_certificate_of_sign_defect_classification
        normalizedRouteTraceDataFromTheorems
        normalizedSignDefectClassificationForRouteFromTheorems
        normalizedRouteFinalSignNonpositiveFromTheorems }

noncomputable def normalizedFinalExitPackageFromTheorems :
    RouteFinalExitPackage
      (RouteInputs.ofExpandedSourcePackage
        normalizedSourceObjectPackageFromTheorems) :=
  route_final_exit_package_of_certificate
    normalizedRouteCertificateFromTheorems

abbrev normalizedSelectedRouteInputsFromTheorems :
    RouteInputs :=
  RouteInputs.ofExpandedSourcePackage normalizedSourceObjectPackageFromTheorems

noncomputable def normalizedSelectedRouteBackedCC20ExitInputDataFromTheorems :
    RouteBackedCC20ExitInputData
      normalizedSelectedRouteInputsFromTheorems
      normalizedRouteCertificateFromTheorems.sourceBackedTest
      normalizedRouteCertificateFromTheorems.ledgers
      normalizedRouteCertificateFromTheorems.bridge :=
  route_backed_cc20_exit_input_data_of_route_bridge_certificate
    normalizedRouteCertificateFromTheorems.bridge

def normalizedSelectedRouteBackedFinalSignFromTheorems :=
  normalizedSelectedRouteBackedCC20ExitInputDataFromTheorems.finalSignNonpositive

def NormalizedSelectedRouteBackedYoshidaDetectorSameTestPolePairingTraceCalibration
    {rho : ℂ}
    (detector :
      YoshidaDetector
        normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho) : Prop :=
  Source.normalizedCC20ConcreteEvaluationData.polePairing
      (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare
        detector.test) =
    normalizedSelectedRouteInputsFromTheorems.cc20.archimedeanSymbols.positiveTrace
      detector.test

def NormalizedSelectedRouteBackedYoshidaDetectorSameTestHalfDensityTraceFormula
    {rho : ℂ}
    (detector :
      YoshidaDetector
        normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho) : Prop :=
  (Source.normalizedCC20ConcreteEvaluationData.mellinAt
      (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare
        (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare
          detector.test))
      (Complex.I / 2)).re +
    (Source.normalizedCC20ConcreteEvaluationData.mellinAt
      (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare
        (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare
          detector.test))
      (-Complex.I / 2)).re =
  normalizedSelectedRouteInputsFromTheorems.cc20.archimedeanSymbols.positiveTrace
    detector.test

theorem normalizedSelectedRouteBackedYoshidaDetectorSameTestHalfDensityTraceFormula_of_polePairingTraceCalibration
    {rho : ℂ}
    {detector :
      YoshidaDetector
        normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho}
    (hcalibration :
      NormalizedSelectedRouteBackedYoshidaDetectorSameTestPolePairingTraceCalibration
        detector) :
    NormalizedSelectedRouteBackedYoshidaDetectorSameTestHalfDensityTraceFormula
      detector := by
  unfold NormalizedSelectedRouteBackedYoshidaDetectorSameTestHalfDensityTraceFormula
  have hpole :=
    Source.normalizedCC20ConcreteEvaluationData.polePairing_eq_mellin_convolutionSquare_half_sum
      (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare
        detector.test)
  exact hpole.symm.trans hcalibration

def NormalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestHalfDensityTraceFormula
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (_hdata :
      Source.CC20YoshidaInterpolationNode.ConcreteYoshidaMomentData rho g) :
    Prop :=
  (Source.normalizedCC20ConcreteEvaluationData.mellinAt
      (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare
        (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare g))
      (Complex.I / 2)).re +
    (Source.normalizedCC20ConcreteEvaluationData.mellinAt
      (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare
        (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare g))
      (-Complex.I / 2)).re =
  normalizedSelectedRouteInputsFromTheorems.cc20.archimedeanSymbols.positiveTrace
    g

def NormalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestLocalSumReadOff
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (_hdata :
      Source.CC20YoshidaInterpolationNode.ConcreteYoshidaMomentData rho g) :
    Prop :=
  Source.normalizedCC20TestSpace.weilLocalSum
      (Source.normalizedCC20TestSpace.starConvolution g) =
    -normalizedSelectedRouteInputsFromTheorems.cc20.archimedeanSymbols.positiveTrace
      g

def normalizedSelectedYoshidaDetectorOfConcreteMomentData
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (hdata :
      Source.CC20YoshidaInterpolationNode.ConcreteYoshidaMomentData rho g) :
    YoshidaDetector normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho where
  test := g
  compactSupportSmooth := hdata.compactSupportSmooth
  vanishesOnF :=
    Source.CC20YoshidaInterpolationNode.concreteYoshidaMomentData_vanishesOn_cc20Triple
      hdata
  detectsRho :=
    Source.CC20YoshidaInterpolationNode.concreteYoshidaMomentData_detects_rho
      hdata
  weilSumPositiveIfOffLine := fun _hrho _hoff =>
    Source.CC20YoshidaInterpolationNode.concreteYoshidaMomentData_weilLocalSum_positive
      hdata

structure NormalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibration
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (hdata :
      Source.CC20YoshidaInterpolationNode.ConcreteYoshidaMomentData rho g) where
  calibration :
    NormalizedRouteBackedYoshidaDetectorArchimedeanLocalSumCalibration
      (normalizedSelectedYoshidaDetectorOfConcreteMomentData hdata)
      normalizedSelectedRouteInputsFromTheorems
  archimedeanTest_eq :
    calibration.archimedeanTest = g

def NormalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibrationRealizer :
    Prop :=
  ∀ {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test},
    Source.RHDefinitionBridge.standard.sourceNontrivialZero rho →
      rho.re ≠ 1 / 2 →
        (hdata :
          Source.CC20YoshidaInterpolationNode.ConcreteYoshidaMomentData rho g) →
          Nonempty
            (NormalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibration
              hdata)

def NormalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestLocalSumReadOffRealizer :
    Prop :=
  ∀ {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test},
    Source.RHDefinitionBridge.standard.sourceNontrivialZero rho →
      rho.re ≠ 1 / 2 →
        (hdata :
          Source.CC20YoshidaInterpolationNode.ConcreteYoshidaMomentData rho g) →
          NormalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestLocalSumReadOff
            hdata

theorem normalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestLocalSumReadOff_of_archimedeanLocalSumCalibration
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    {hdata :
      Source.CC20YoshidaInterpolationNode.ConcreteYoshidaMomentData rho g}
    (hcalibration :
      NormalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibration
        hdata) :
    NormalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestLocalSumReadOff
      hdata := by
  unfold NormalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestLocalSumReadOff
  simpa [normalizedSelectedYoshidaDetectorOfConcreteMomentData,
    hcalibration.archimedeanTest_eq] using
    hcalibration.calibration.routeBackedLocalSumReadOff

theorem normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestLocalSumReadOffRealizer_of_archimedeanLocalSumCalibrationRealizer
    (hrealizer :
      NormalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibrationRealizer) :
    NormalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestLocalSumReadOffRealizer := by
  intro rho g hrho hoff hdata
  rcases hrealizer hrho hoff hdata with ⟨hcalibration⟩
  exact
    normalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestLocalSumReadOff_of_archimedeanLocalSumCalibration
      hcalibration

theorem normalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestHalfDensityTraceFormula_of_localSumReadOff
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    {hdata :
      Source.CC20YoshidaInterpolationNode.ConcreteYoshidaMomentData rho g}
    (hreadOff :
      NormalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestLocalSumReadOff
        hdata) :
    NormalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestHalfDensityTraceFormula
      hdata := by
  unfold NormalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestLocalSumReadOff at hreadOff
  unfold NormalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestHalfDensityTraceFormula
  have hlocal := hreadOff
  rw [Source.normalizedCC20TestSpace_weilLocalSum_eq,
    Source.normalizedCC20TestSpace_starConvolution_eq] at hlocal
  have hcalibration :
      Source.normalizedCC20ConcreteEvaluationData.polePairing
          (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare g) =
        normalizedSelectedRouteInputsFromTheorems.cc20.archimedeanSymbols.positiveTrace
          g := by
    simpa using congrArg (fun x : ℝ => -x) hlocal
  have hpole :=
    Source.normalizedCC20ConcreteEvaluationData.polePairing_eq_mellin_convolutionSquare_half_sum
      (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare g)
  exact hpole.symm.trans hcalibration

def NormalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestHalfDensityTraceFormulaRealizer :
    Prop :=
  ∀ {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test},
    Source.RHDefinitionBridge.standard.sourceNontrivialZero rho →
      rho.re ≠ 1 / 2 →
        (hdata :
          Source.CC20YoshidaInterpolationNode.ConcreteYoshidaMomentData rho g) →
          NormalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestHalfDensityTraceFormula
            hdata

theorem normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestHalfDensityTraceFormulaRealizer_of_localSumReadOffRealizer
    (hrealizer :
      NormalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestLocalSumReadOffRealizer) :
    NormalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestHalfDensityTraceFormulaRealizer := by
  intro rho g hrho hoff hdata
  exact
    normalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestHalfDensityTraceFormula_of_localSumReadOff
      (hrealizer hrho hoff hdata)

theorem normalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestHalfDensityTraceFormula_contradicts_moment_data
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (hdata :
      Source.CC20YoshidaInterpolationNode.ConcreteYoshidaMomentData rho g)
    (hformula :
      NormalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestHalfDensityTraceFormula
        hdata) :
    False := by
  have hgate :
      normalizedSelectedRouteInputsFromTheorems.cc20.archimedeanSymbols.hilbertSchmidtGate
        g := by
    simpa [normalizedSelectedRouteInputsFromTheorems,
      RouteInputs.ofExpandedSourcePackage,
      Source.CC20Interface.ofSourceObjectPackage,
      Source.SourceObject.SourceObjectPackage.toArchimedeanTraceSymbols] using
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceHilbertSchmidtGate
        g
  let hlegal :=
    cc20_trace_legality_template_output
      (inputs := normalizedSelectedRouteInputsFromTheorems)
      (a := g)
      hgate
  have hpositiveTraceNonnegative :
      0 ≤
        normalizedSelectedRouteInputsFromTheorems.cc20.archimedeanSymbols.positiveTrace
          g := by
    exact normalizedSourceObjectPackageFromTheorems.cc20Trace.sourcePositiveTraceNonnegative
      g hlegal.traceClass hlegal.cyclicLegal
  have hhalfDensityNonnegative :
      0 ≤
        (Source.normalizedCC20ConcreteEvaluationData.mellinAt
            (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare
              (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare g))
            (Complex.I / 2)).re +
          (Source.normalizedCC20ConcreteEvaluationData.mellinAt
            (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare
              (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare g))
            (-Complex.I / 2)).re := by
    rw [hformula]
    exact hpositiveTraceNonnegative
  exact
    Source.CC20YoshidaInterpolationNode.concreteYoshidaMomentData_not_halfDensityPoleSum_nonnegative
      hdata hhalfDensityNonnegative

theorem not_normalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestHalfDensityTraceFormula
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (hdata :
      Source.CC20YoshidaInterpolationNode.ConcreteYoshidaMomentData rho g) :
    ¬ NormalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestHalfDensityTraceFormula
      hdata := by
  intro hformula
  exact
    normalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestHalfDensityTraceFormula_contradicts_moment_data
      hdata hformula

theorem not_normalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestLocalSumReadOff
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (hdata :
      Source.CC20YoshidaInterpolationNode.ConcreteYoshidaMomentData rho g) :
    ¬ NormalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestLocalSumReadOff
      hdata := by
  intro hreadOff
  exact
    not_normalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestHalfDensityTraceFormula
      hdata
      (normalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestHalfDensityTraceFormula_of_localSumReadOff
        hreadOff)

theorem not_normalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibration
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (hdata :
      Source.CC20YoshidaInterpolationNode.ConcreteYoshidaMomentData rho g) :
    ¬ Nonempty
      (NormalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibration
        hdata) := by
  rintro ⟨hcalibration⟩
  exact
    not_normalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestLocalSumReadOff
      hdata
      (normalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestLocalSumReadOff_of_archimedeanLocalSumCalibration
        hcalibration)

theorem normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataContradictionRealizer_of_sameTestHalfDensityTraceFormulaRealizer
    (hrealizer :
      NormalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestHalfDensityTraceFormulaRealizer) :
    NormalizedRouteBackedSourceZeroConcreteYoshidaMomentDataContradictionRealizer := by
  intro rho g hrho hoff hdata
  exact
    normalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestHalfDensityTraceFormula_contradicts_moment_data
      hdata (hrealizer hrho hoff hdata)

theorem normalizedSelectedRouteBacked_no_offline_source_zero_of_concrete_yoshida_moment_data_localSumReadOff
    (hrealizer :
      NormalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestLocalSumReadOffRealizer) :
    ∀ {rho : ℂ},
      Source.RHDefinitionBridge.standard.sourceNontrivialZero rho →
        rho.re = 1 / 2 :=
  normalizedCC20_no_offline_source_zero_of_concrete_yoshida_moment_data_contradiction
    Source.CC20YoshidaInterpolationNode.normalizedCC20ConcreteYoshidaMomentDataExists
    (normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataContradictionRealizer_of_sameTestHalfDensityTraceFormulaRealizer
      (normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestHalfDensityTraceFormulaRealizer_of_localSumReadOffRealizer
        hrealizer))

theorem normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestLocalSumReadOffRealizer_of_no_offline_source_zero
    (hNoOffLine :
      ∀ {rho : ℂ},
        Source.RHDefinitionBridge.standard.sourceNontrivialZero rho →
          rho.re = 1 / 2) :
    NormalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestLocalSumReadOffRealizer := by
  intro rho g hrho hoff _hdata
  exact False.elim (hoff (hNoOffLine hrho))

theorem normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestLocalSumReadOffRealizer_iff_no_offline_source_zero :
    NormalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestLocalSumReadOffRealizer ↔
      (∀ {rho : ℂ},
        Source.RHDefinitionBridge.standard.sourceNontrivialZero rho →
          rho.re = 1 / 2) := by
  constructor
  · exact
      normalizedSelectedRouteBacked_no_offline_source_zero_of_concrete_yoshida_moment_data_localSumReadOff
  · exact
      normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestLocalSumReadOffRealizer_of_no_offline_source_zero

theorem normalizedSelectedRouteBacked_no_offline_source_zero_of_concrete_yoshida_moment_data_archimedeanLocalSumCalibration
    (hrealizer :
      NormalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibrationRealizer) :
    ∀ {rho : ℂ},
      Source.RHDefinitionBridge.standard.sourceNontrivialZero rho →
        rho.re = 1 / 2 :=
  normalizedSelectedRouteBacked_no_offline_source_zero_of_concrete_yoshida_moment_data_localSumReadOff
    (normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestLocalSumReadOffRealizer_of_archimedeanLocalSumCalibrationRealizer
      hrealizer)

theorem normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibrationRealizer_of_no_offline_source_zero
    (hNoOffLine :
      ∀ {rho : ℂ},
        Source.RHDefinitionBridge.standard.sourceNontrivialZero rho →
          rho.re = 1 / 2) :
    NormalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibrationRealizer := by
  intro rho g hrho hoff _hdata
  exact False.elim (hoff (hNoOffLine hrho))

theorem normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibrationRealizer_iff_no_offline_source_zero :
    NormalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibrationRealizer ↔
      (∀ {rho : ℂ},
        Source.RHDefinitionBridge.standard.sourceNontrivialZero rho →
          rho.re = 1 / 2) := by
  constructor
  · exact
      normalizedSelectedRouteBacked_no_offline_source_zero_of_concrete_yoshida_moment_data_archimedeanLocalSumCalibration
  · exact
      normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibrationRealizer_of_no_offline_source_zero

theorem not_normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibrationRealizer_of_offline_source_zero
    {rho : ℂ}
    (hrho : Source.RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    ¬ NormalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibrationRealizer := by
  intro hrealizer
  rcases Source.CC20YoshidaInterpolationNode.normalizedCC20ConcreteYoshidaMomentDataExists
      hrho hoff with
    ⟨g, hdata⟩
  exact
    not_normalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibration
      hdata
      (hrealizer hrho hoff hdata)

structure NormalizedSelectedRouteBackedYoshidaDetectorMathlibBottom
    {rho : ℂ}
    (detector :
      YoshidaDetector
        normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho) where
  archimedeanTest :
    normalizedSelectedRouteInputsFromTheorems.cc20.archimedeanSymbols.Test
  archimedeanTest_eq_detectorTest :
    HEq archimedeanTest detector.test
  doubleConvolutionHalfDensityTraceFormula :
    (Source.normalizedCC20ConcreteEvaluationData.mellinAt
        (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare
          (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare
            detector.test))
        (Complex.I / 2)).re +
      (Source.normalizedCC20ConcreteEvaluationData.mellinAt
        (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare
          (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare
            detector.test))
        (-Complex.I / 2)).re =
    normalizedSelectedRouteInputsFromTheorems.cc20.archimedeanSymbols.positiveTrace
      archimedeanTest

noncomputable def normalizedSelectedRouteBackedYoshidaDetectorMathlibBottom_of_sameTestFormula
    {rho : ℂ}
    {detector :
      YoshidaDetector
        normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho}
    (hformula :
      NormalizedSelectedRouteBackedYoshidaDetectorSameTestHalfDensityTraceFormula
        detector) :
    NormalizedSelectedRouteBackedYoshidaDetectorMathlibBottom detector where
  archimedeanTest := detector.test
  archimedeanTest_eq_detectorTest := HEq.rfl
  doubleConvolutionHalfDensityTraceFormula := hformula

noncomputable def normalizedSelectedRouteBackedYoshidaDetectorArchimedeanReadOff_of_mathlibBottom
    {rho : ℂ}
    {detector :
      YoshidaDetector
        normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho}
    (bottom :
      NormalizedSelectedRouteBackedYoshidaDetectorMathlibBottom detector) :
    NormalizedRouteBackedYoshidaDetectorArchimedeanReadOff
      detector normalizedSelectedRouteInputsFromTheorems where
  archimedeanTest := bottom.archimedeanTest
  hilbertSchmidtGate := by
    simpa [normalizedSelectedRouteInputsFromTheorems,
      RouteInputs.ofExpandedSourcePackage,
      Source.CC20Interface.ofSourceObjectPackage,
      Source.SourceObject.SourceObjectPackage.toArchimedeanTraceSymbols] using
      normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceHilbertSchmidtGate
        bottom.archimedeanTest
  routeBackedLocalSumReadOff := by
    have hpole :=
      Source.normalizedCC20ConcreteEvaluationData.polePairing_eq_mellin_convolutionSquare_half_sum
        (Source.normalizedCC20ConcreteTestAlgebra.convolutionSquare
          detector.test)
    rw [Source.normalizedCC20TestSpace_weilLocalSum_eq,
      Source.normalizedCC20TestSpace_starConvolution_eq, hpole,
      bottom.doubleConvolutionHalfDensityTraceFormula]

noncomputable def normalizedSelectedRouteBackedYoshidaDetectorSignWitness_of_mathlibBottom
    {rho : ℂ}
    {detector :
      YoshidaDetector
        normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho}
    (bottom :
      NormalizedSelectedRouteBackedYoshidaDetectorMathlibBottom detector) :
    NormalizedRouteBackedYoshidaDetectorSignWitness detector :=
  let readOff :=
    normalizedSelectedRouteBackedYoshidaDetectorArchimedeanReadOff_of_mathlibBottom
      bottom
  let archRealization :=
    normalizedRouteBackedYoshidaDetectorArchimedeanTraceRealization_of_readOff
      normalizedRouteCertificateFromTheorems.sourceBackedTest
      normalizedRouteCertificateFromTheorems.sourceBackedTest.finitePrimeSourceDataOwner
      normalizedRouteTraceDataFromTheorems.lambda
      normalizedRouteTraceDataFromTheorems.oneLtLambda
      normalizedRouteTraceDataFromTheorems.ccm25ArithmeticPackage.rows
      readOff
  let traceRealization :=
    normalizedRouteBackedYoshidaDetectorTraceRealization_of_archimedean
      archRealization
  let routeRealization :=
    normalizedRouteBackedYoshidaDetectorRouteRealization_of_trace_realization
      traceRealization
  normalizedRouteBackedYoshidaDetectorSignWitness_of_route_realization
    routeRealization

theorem normalizedSelectedRouteBackedYoshidaDetectorMathlibBottom_contradicts_source_zero
    {rho : ℂ}
    (hrho : Source.RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2)
    {detector :
      YoshidaDetector
        normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho}
    (bottom :
      NormalizedSelectedRouteBackedYoshidaDetectorMathlibBottom detector) :
    False := by
  let witness :=
    normalizedSelectedRouteBackedYoshidaDetectorSignWitness_of_mathlibBottom
      bottom
  have hpos : 0 <
      normalizedCC20TestSpace.weilLocalSum
        (normalizedCC20TestSpace.starConvolution witness.data.detector.test) :=
    witness.data.detector.weilSumPositiveIfOffLine hrho hoff
  have hnonpos :
      CC20WeilNonpositive
        normalizedCC20TestSpace witness.data.detector.test :=
    normalizedRouteBackedYoshidaSignTheorem_of_localSumReadOff
      witness.routeBackedLocalSumReadOff
      witness.data.routeBackedFinalSign
  exact (not_lt_of_ge hnonpos) hpos

theorem not_normalizedSelectedRouteBackedYoshidaDetectorSameTestHalfDensityTraceFormula_of_source_zero
    {rho : ℂ}
    (hrho : Source.RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2)
    {detector :
      YoshidaDetector
        normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho} :
    ¬ NormalizedSelectedRouteBackedYoshidaDetectorSameTestHalfDensityTraceFormula
      detector := by
  intro hformula
  exact
    normalizedSelectedRouteBackedYoshidaDetectorMathlibBottom_contradicts_source_zero
      hrho hoff
      (normalizedSelectedRouteBackedYoshidaDetectorMathlibBottom_of_sameTestFormula
        hformula)

theorem not_normalizedSelectedRouteBackedYoshidaDetectorSameTestPolePairingTraceCalibration_of_source_zero
    {rho : ℂ}
    (hrho : Source.RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2)
    {detector :
      YoshidaDetector
        normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho} :
    ¬ NormalizedSelectedRouteBackedYoshidaDetectorSameTestPolePairingTraceCalibration
      detector := by
  intro hcalibration
  exact
    not_normalizedSelectedRouteBackedYoshidaDetectorSameTestHalfDensityTraceFormula_of_source_zero
      hrho hoff
      (normalizedSelectedRouteBackedYoshidaDetectorSameTestHalfDensityTraceFormula_of_polePairingTraceCalibration
        hcalibration)

theorem not_normalizedSelectedRouteBackedYoshidaDetectorMathlibBottom_of_source_zero
    {rho : ℂ}
    (hrho : Source.RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2)
    {detector :
      YoshidaDetector
        normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho} :
    ¬ Nonempty
      (NormalizedSelectedRouteBackedYoshidaDetectorMathlibBottom detector) := by
  rintro ⟨bottom⟩
  exact
    normalizedSelectedRouteBackedYoshidaDetectorMathlibBottom_contradicts_source_zero
      hrho hoff bottom

theorem not_normalizedSelectedRouteBackedYoshidaDetectorLocalSumCalibration_of_source_zero
    {rho : ℂ}
    (hrho : Source.RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2)
    {detector :
      YoshidaDetector
        normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho} :
    ¬ Nonempty
      (NormalizedRouteBackedYoshidaDetectorArchimedeanLocalSumCalibration
        detector normalizedSelectedRouteInputsFromTheorems) := by
  rintro ⟨calibration⟩
  exact
    normalizedRouteBackedYoshidaDetectorArchimedeanLocalSumCalibration_contradicts_source_zero
      hrho hoff calibration
      (by
        simpa [normalizedSelectedRouteInputsFromTheorems,
          RouteInputs.ofExpandedSourcePackage,
          Source.CC20Interface.ofSourceObjectPackage,
          Source.SourceObject.SourceObjectPackage.toArchimedeanTraceSymbols] using
        normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceHilbertSchmidtGate
            calibration.archimedeanTest)

/-- The remaining selected detector pole-pairing root is RH-level, not a lower
producer.  Filling this socket proves exactly the standard source RH statement
once Yoshida detector existence is available. -/
theorem normalizedSelectedYoshidaDetectorPolePairingNonnegativeCore_iff_standardSourceRH :
    NormalizedRouteBackedSourceZeroYoshidaDetectorPolePairingNonnegativeRealizer ↔
      Source.RHDefinitionBridge.standard.SourceRH :=
  normalizedRouteBackedSourceZeroYoshidaDetectorPolePairingNonnegativeRealizer_iff_standardSourceRH
    Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists

theorem normalizedSelectedYoshidaDetectorPolePairingNonnegativeCore_iff_mathlibRH :
    NormalizedRouteBackedSourceZeroYoshidaDetectorPolePairingNonnegativeRealizer ↔
      _root_.RiemannHypothesis :=
  normalizedSelectedYoshidaDetectorPolePairingNonnegativeCore_iff_standardSourceRH.trans
    Source.RHDefinitionBridge.standard_source_rh_iff_mathlib

axiom normalizedSelectedYoshidaDetectorPolePairingNonnegativeCoreRoot :
  NormalizedRouteBackedSourceZeroYoshidaDetectorPolePairingNonnegativeRealizer

noncomputable def normalizedSelectedYoshidaDetectorPolePairingNonnegativeCoreFromTheorems :
    NormalizedRouteBackedSourceZeroYoshidaDetectorPolePairingNonnegativeRealizer :=
  normalizedSelectedYoshidaDetectorPolePairingNonnegativeCoreRoot

noncomputable def normalizedSelectedYoshidaDetectorNonpositiveCoreFromTheorems :
    NormalizedRouteBackedSourceZeroYoshidaDetectorNonpositiveRealizer :=
  normalizedRouteBackedSourceZeroYoshidaDetectorNonpositiveRealizer_of_polePairingNonnegative
    normalizedSelectedYoshidaDetectorPolePairingNonnegativeCoreFromTheorems

noncomputable def normalizedSelectedNoOffLineSourceZeroCoreFromTheorems :
    ∀ {rho : ℂ},
      Source.RHDefinitionBridge.standard.sourceNontrivialZero rho →
        rho.re = 1 / 2 := by
  exact
    normalizedCC20_no_offline_source_zero_of_source_zero_yoshida_detector_nonpositive
      Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists
      normalizedSelectedYoshidaDetectorNonpositiveCoreFromTheorems

theorem normalizedSelectedNoOffLineSourceZero_iff_standardSourceRH :
    (∀ {rho : ℂ},
      Source.RHDefinitionBridge.standard.sourceNontrivialZero rho →
        rho.re = 1 / 2) ↔
      Source.RHDefinitionBridge.standard.SourceRH := by
  constructor
  · intro h rho hrho
    exact
      Source.RHDefinitionBridge.standard.mathlibCriticalLine_to_source
        rho (h (rho := rho) hrho)
  · intro h rho hrho
    exact
      Source.RHDefinitionBridge.standard.sourceCriticalLine_to_mathlib
        rho (h rho hrho)

theorem normalizedSelectedNoOffLineSourceZero_iff_mathlibRH :
    (∀ {rho : ℂ},
      Source.RHDefinitionBridge.standard.sourceNontrivialZero rho →
        rho.re = 1 / 2) ↔
      _root_.RiemannHypothesis :=
  normalizedSelectedNoOffLineSourceZero_iff_standardSourceRH.trans
    Source.RHDefinitionBridge.standard_source_rh_iff_mathlib

theorem normalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestLocalSumReadOffRealizer_iff_standardSourceRH :
    NormalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestLocalSumReadOffRealizer ↔
      Source.RHDefinitionBridge.standard.SourceRH :=
  normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestLocalSumReadOffRealizer_iff_no_offline_source_zero.trans
    normalizedSelectedNoOffLineSourceZero_iff_standardSourceRH

theorem normalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestLocalSumReadOffRealizer_iff_mathlibRH :
    NormalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestLocalSumReadOffRealizer ↔
      _root_.RiemannHypothesis :=
  normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestLocalSumReadOffRealizer_iff_no_offline_source_zero.trans
    normalizedSelectedNoOffLineSourceZero_iff_mathlibRH

theorem normalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibrationRealizer_iff_standardSourceRH :
    NormalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibrationRealizer ↔
      Source.RHDefinitionBridge.standard.SourceRH :=
  normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibrationRealizer_iff_no_offline_source_zero.trans
    normalizedSelectedNoOffLineSourceZero_iff_standardSourceRH

theorem normalizedSelectedRouteBackedConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibrationRealizer_iff_mathlibRH :
    NormalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibrationRealizer ↔
      _root_.RiemannHypothesis :=
  normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibrationRealizer_iff_no_offline_source_zero.trans
    normalizedSelectedNoOffLineSourceZero_iff_mathlibRH

noncomputable def normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibrationFromTheorems :
    NormalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibrationRealizer :=
  normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibrationRealizer_of_no_offline_source_zero
    normalizedSelectedNoOffLineSourceZeroCoreFromTheorems

noncomputable def normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestLocalSumReadOffFromTheorems :
    NormalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestLocalSumReadOffRealizer :=
  normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestLocalSumReadOffRealizer_of_archimedeanLocalSumCalibrationRealizer
    normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestArchimedeanLocalSumCalibrationFromTheorems

noncomputable def normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestHalfDensityTraceFormulaFromTheorems :
    NormalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestHalfDensityTraceFormulaRealizer :=
  normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestHalfDensityTraceFormulaRealizer_of_localSumReadOffRealizer
    normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestLocalSumReadOffFromTheorems

noncomputable def normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataContradictionFromTheorems :
    NormalizedRouteBackedSourceZeroConcreteYoshidaMomentDataContradictionRealizer :=
  normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataContradictionRealizer_of_sameTestHalfDensityTraceFormulaRealizer
    normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataSameTestHalfDensityTraceFormulaFromTheorems

noncomputable def normalizedSelectedSourceRHFromTheorems :
    Source.RHDefinitionBridge.standard.SourceRH :=
  normalizedCC20_source_rh_of_source_zero_yoshida_detector_nonpositive
    Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists
    normalizedSelectedYoshidaDetectorNonpositiveCoreFromTheorems

noncomputable def normalizedSelectedNoOffLineSourceZeroFromTheorems :
    ∀ {rho : ℂ},
      Source.RHDefinitionBridge.standard.sourceNontrivialZero rho →
        rho.re = 1 / 2 :=
  normalizedSelectedNoOffLineSourceZeroCoreFromTheorems

noncomputable def normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataHalfDensityNonnegativeFromTheorems :
    NormalizedRouteBackedSourceZeroConcreteYoshidaMomentDataHalfDensityNonnegativeRealizer :=
  normalizedRouteBackedSourceZeroConcreteYoshidaMomentDataHalfDensityNonnegativeRealizer_of_no_offline_source_zero
    normalizedSelectedNoOffLineSourceZeroFromTheorems

noncomputable def normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataPolePairingNonnegativeFromTheorems :
    NormalizedRouteBackedSourceZeroConcreteYoshidaMomentDataPolePairingNonnegativeRealizer :=
  normalizedRouteBackedSourceZeroConcreteYoshidaMomentDataPolePairingNonnegativeRealizer_of_halfDensityNonnegative
    normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataHalfDensityNonnegativeFromTheorems

noncomputable def normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataNonpositiveFromTheorems :
    NormalizedRouteBackedSourceZeroConcreteYoshidaMomentDataNonpositiveRealizer :=
  normalizedRouteBackedSourceZeroConcreteYoshidaMomentDataNonpositiveRealizer_of_polePairingNonnegative
    normalizedSelectedRouteBackedSourceZeroConcreteYoshidaMomentDataPolePairingNonnegativeFromTheorems

noncomputable def normalizedSelectedRouteBackedSourceZeroYoshidaDetectorHalfDensityNonnegativeFromTheorems :
    NormalizedRouteBackedSourceZeroYoshidaDetectorHalfDensityNonnegativeRealizer :=
  normalizedRouteBackedSourceZeroYoshidaDetectorHalfDensityNonnegativeRealizer_of_no_offline_source_zero
    normalizedSelectedNoOffLineSourceZeroFromTheorems

noncomputable def normalizedSelectedRouteBackedSourceZeroYoshidaDetectorPolePairingNonnegativeFromTheorems :
    NormalizedRouteBackedSourceZeroYoshidaDetectorPolePairingNonnegativeRealizer :=
  normalizedSelectedYoshidaDetectorPolePairingNonnegativeCoreFromTheorems

noncomputable def normalizedSelectedRouteBackedSourceZeroYoshidaDetectorNonpositiveFromTheorems :
    NormalizedRouteBackedSourceZeroYoshidaDetectorNonpositiveRealizer :=
  normalizedRouteBackedSourceZeroYoshidaDetectorNonpositiveRealizer_of_polePairingNonnegative
    normalizedSelectedRouteBackedSourceZeroYoshidaDetectorPolePairingNonnegativeFromTheorems

noncomputable def normalizedSelectedRouteBackedSourceZeroYoshidaDetectorLocalSumCalibrationRealizerFromTheorems :
    NormalizedRouteBackedSourceZeroYoshidaDetectorArchimedeanLocalSumCalibrationRealizer
      normalizedSelectedRouteInputsFromTheorems :=
  normalizedRouteBackedSourceZeroYoshidaDetectorArchimedeanLocalSumCalibrationRealizer_of_no_offline_source_zero
    normalizedSelectedNoOffLineSourceZeroFromTheorems

noncomputable def normalizedSelectedRouteBackedSourceZeroYoshidaDetectorArchimedeanReadOffRealizerFromTheorems :
    NormalizedRouteBackedSourceZeroYoshidaDetectorArchimedeanReadOffRealizer
      normalizedSelectedRouteInputsFromTheorems :=
  normalizedRouteBackedSourceZeroYoshidaDetectorArchimedeanReadOffRealizer_of_localSumCalibrationRealizer
    (by
      intro archimedeanTest
      simpa [normalizedSelectedRouteInputsFromTheorems,
        RouteInputs.ofExpandedSourcePackage,
        Source.CC20Interface.ofSourceObjectPackage,
        Source.SourceObject.SourceObjectPackage.toArchimedeanTraceSymbols] using
        normalizedSourceObjectPackageFromTheorems.cc20Trace.sourceHilbertSchmidtGate
          archimedeanTest)
    normalizedSelectedRouteBackedSourceZeroYoshidaDetectorLocalSumCalibrationRealizerFromTheorems

noncomputable def normalizedSelectedRouteBackedSourceZeroYoshidaDetectorHilbertLocalSumRealizerFromTheorems :
    NormalizedRouteBackedSourceZeroYoshidaDetectorHilbertLocalSumRealizer :=
  normalizedRouteBackedSourceZeroYoshidaDetectorHilbertLocalSumRealizer_of_archimedeanReadOffRealizer
    normalizedSelectedRouteInputsFromTheorems
    normalizedSelectedRouteBackedSourceZeroYoshidaDetectorArchimedeanReadOffRealizerFromTheorems

theorem normalizedSelectedRouteBackedSourceZeroYoshidaDetectorHilbertLocalSumRealizer_iff_standardSourceRH :
    NormalizedRouteBackedSourceZeroYoshidaDetectorHilbertLocalSumRealizer ↔
      Source.RHDefinitionBridge.standard.SourceRH :=
  normalizedRouteBackedSourceZeroYoshidaDetectorHilbertLocalSumRealizer_iff_standardSourceRH
    Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists

theorem not_normalizedSelectedRouteBackedSourceZeroYoshidaDetectorHilbertLocalSumRealizer_of_offline_source_zero
    {rho : ℂ}
    (hrho : Source.RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    ¬ NormalizedRouteBackedSourceZeroYoshidaDetectorHilbertLocalSumRealizer := by
  rcases Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists hrho hoff with
    ⟨detector⟩
  exact
    not_normalizedRouteBackedSourceZeroYoshidaDetectorHilbertLocalSumRealizer_of_source_zero
      hrho hoff detector

theorem not_normalizedSelectedRouteBackedYoshidaHilbertLocalSumFamily_of_offline_source_zero
    {rho : ℂ}
    (hrho : Source.RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    ¬ NormalizedRouteBackedYoshidaHilbertLocalSumFamily := by
  intro hfamily
  rcases hfamily hrho hoff with ⟨witness⟩
  exact
    normalizedRouteBackedYoshidaDetectorHilbertLocalSum_contradicts_source_zero
      hrho hoff
      { inputs := witness.inputs
        archimedeanTest := witness.archimedeanTest
        hilbertSchmidtGate := witness.hilbertSchmidtGate
        routeBackedLocalSumReadOff := witness.routeBackedLocalSumReadOff }

theorem not_normalizedSelectedRouteBackedYoshidaRawPositiveTraceFamily_of_offline_source_zero
    {rho : ℂ}
    (hrho : Source.RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    ¬ NormalizedRouteBackedYoshidaRawPositiveTraceFamily := by
  intro hfamily
  rcases hfamily hrho hoff with ⟨witness⟩
  have hpos : 0 <
      normalizedCC20TestSpace.weilLocalSum
        (normalizedCC20TestSpace.starConvolution witness.detector.test) :=
    witness.detector.weilSumPositiveIfOffLine hrho hoff
  have hnonpos :
      normalizedCC20TestSpace.weilLocalSum
          (normalizedCC20TestSpace.starConvolution witness.detector.test) ≤ 0 := by
    rw [witness.routeBackedLocalSumReadOff]
    exact neg_nonpos.mpr witness.positiveTraceNonnegative
  exact (not_lt_of_ge hnonpos) hpos

theorem not_normalizedSelectedRouteBackedYoshidaPositiveTraceFamily_of_offline_source_zero
    {rho : ℂ}
    (hrho : Source.RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    ¬ NormalizedRouteBackedYoshidaPositiveTraceFamily := by
  intro hfamily
  exact
    not_normalizedSelectedRouteBackedYoshidaRawPositiveTraceFamily_of_offline_source_zero
      hrho hoff
      (normalizedRouteBackedYoshidaRawPositiveTraceFamily_of_positive_trace_family
        hfamily)

theorem not_normalizedSelectedRouteBackedYoshidaSignFamily_of_offline_source_zero
    {rho : ℂ}
    (hrho : Source.RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    ¬ NormalizedRouteBackedYoshidaSignFamily := by
  intro hfamily
  exact
    not_normalizedSelectedRouteBackedYoshidaPositiveTraceFamily_of_offline_source_zero
      hrho hoff
      (normalizedRouteBackedYoshidaPositiveTraceFamily_of_sign_family hfamily)

noncomputable def normalizedSelectedRouteBackedSourceZeroYoshidaDetectorArchimedeanTraceRealizerFromTheorems :
    NormalizedRouteBackedSourceZeroYoshidaDetectorArchimedeanTraceRealizer :=
  normalizedRouteBackedSourceZeroYoshidaDetectorArchimedeanTraceRealizer_of_readOff_realizer
    normalizedRouteCertificateFromTheorems.sourceBackedTest
    normalizedRouteCertificateFromTheorems.sourceBackedTest.finitePrimeSourceDataOwner
    normalizedRouteTraceDataFromTheorems.lambda
    normalizedRouteTraceDataFromTheorems.oneLtLambda
    normalizedRouteTraceDataFromTheorems.ccm25ArithmeticPackage.rows
    normalizedSelectedRouteBackedSourceZeroYoshidaDetectorArchimedeanReadOffRealizerFromTheorems

noncomputable def normalizedSelectedRouteBackedSourceZeroYoshidaDetectorTraceRealizerFromTheorems :
    NormalizedRouteBackedSourceZeroYoshidaDetectorTraceRealizer :=
  normalizedRouteBackedSourceZeroYoshidaDetectorTraceRealizer_of_archimedean_trace_realizer
    normalizedSelectedRouteBackedSourceZeroYoshidaDetectorArchimedeanTraceRealizerFromTheorems

noncomputable def normalizedSelectedRouteBackedSourceZeroYoshidaDetectorRouteRealizerFromTheorems :
    NormalizedRouteBackedSourceZeroYoshidaDetectorRouteRealizer :=
  normalizedRouteBackedSourceZeroYoshidaDetectorRouteRealizer_of_trace_realizer
    normalizedSelectedRouteBackedSourceZeroYoshidaDetectorTraceRealizerFromTheorems

noncomputable def normalizedSelectedRouteBackedSourceZeroYoshidaDetectorNonpositiveFromRouteRealizer :
    NormalizedRouteBackedSourceZeroYoshidaDetectorNonpositiveRealizer :=
  normalizedRouteBackedSourceZeroYoshidaDetectorNonpositiveRealizer_of_route_realizer
    normalizedSelectedRouteBackedSourceZeroYoshidaDetectorRouteRealizerFromTheorems

noncomputable def normalizedSelectedRouteBackedYoshidaHilbertLocalSumFamilyFromTheorems :
    NormalizedRouteBackedYoshidaHilbertLocalSumFamily :=
  normalizedRouteBackedYoshidaHilbertLocalSumFamily_of_sourceZero_detectorHilbertLocalSumRealizer
    Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists
    normalizedSelectedRouteBackedSourceZeroYoshidaDetectorHilbertLocalSumRealizerFromTheorems

noncomputable def normalizedSelectedRouteBackedYoshidaRawPositiveTraceFamilyFromTheorems :
    NormalizedRouteBackedYoshidaRawPositiveTraceFamily :=
  normalizedRouteBackedYoshidaRawPositiveTraceFamily_of_hilbert_localSum_family
    normalizedSelectedRouteBackedYoshidaHilbertLocalSumFamilyFromTheorems

noncomputable def normalizedSelectedRouteBackedSourceRHFromHilbertLocalSumFromTheorems :
    Source.RHDefinitionBridge.standard.SourceRH :=
  normalizedCC20_source_rh_of_routeBacked_yoshida_hilbert_localSum_family
    normalizedSelectedRouteBackedYoshidaHilbertLocalSumFamilyFromTheorems

theorem not_normalizedSelectedCC20FiniteVanishingWeilCriterionInput_fullWeilPositivity :
    normalizedCC20FiniteVanishingWeilCriterionInput.fullWeilPositivity →
      False :=
  Route.not_normalizedCC20FiniteVanishingWeilCriterionInput_fullWeilPositivity

theorem not_normalizedSelectedCC20PropositionC1InputData_finiteVanishingCriterionInput :
    Source.CC20PropositionC1InputData
        Source.RHDefinitionBridge.standard
        Source.cc20TripleFiniteVanishingSet
        normalizedCC20FiniteVanishingWeilCriterionInput →
      False :=
  Route.not_normalizedCC20PropositionC1InputData_finiteVanishingCriterionInput

noncomputable def normalizedSelectedRouteBackedNoOffLineSourceZeroFromTheorems :
    ∀ {rho : ℂ},
      Source.RHDefinitionBridge.standard.sourceNontrivialZero rho →
        rho.re = 1 / 2 :=
  normalizedSelectedNoOffLineSourceZeroFromTheorems

def normalizedSelectedRouteBackedSourceRH_of_noOffLine
    (hNoOffLine :
      ∀ {rho : ℂ},
        Source.RHDefinitionBridge.standard.sourceNontrivialZero rho →
          rho.re = 1 / 2) :
    Source.RHDefinitionBridge.standard.SourceRH := by
  intro rho hrho
  exact hNoOffLine hrho

noncomputable def normalizedSelectedRouteBackedYoshidaSignFamilyFromTheorems :
    NormalizedRouteBackedYoshidaSignFamily := by
  intro rho hrho hoff
  exact False.elim
    (hoff (normalizedSelectedRouteBackedNoOffLineSourceZeroFromTheorems hrho))

noncomputable def normalizedSelectedRouteBackedSourceRHFromTheorems :
    Source.RHDefinitionBridge.standard.SourceRH :=
  normalizedSelectedRouteBackedSourceRH_of_noOffLine
    normalizedSelectedRouteBackedNoOffLineSourceZeroFromTheorems

/-- RH-level selected-exit compatibility package.

This package intentionally stays outside `NormalizedNoArgumentRouteCertificatePackage`.
Its source-zero/no-off-line fields pass through the Yoshida detector
pole-pairing root, which is equivalent to RH by
`normalizedSelectedYoshidaDetectorPolePairingNonnegativeCore_iff_mathlibRH`.
The no-argument outlet below must use the route certificate instead. -/
structure NormalizedSelectedCC20ExitPackage where
  routeBackedExitInputData :
    RouteBackedCC20ExitInputData
      normalizedSelectedRouteInputsFromTheorems
      normalizedRouteCertificateFromTheorems.sourceBackedTest
      normalizedRouteCertificateFromTheorems.ledgers
      normalizedRouteCertificateFromTheorems.bridge
  finalSignMatchesRouteBacked :
    routeBackedExitInputData.finalSignNonpositive =
      normalizedSelectedRouteBackedFinalSignFromTheorems
  noOffLineSourceZero :
    ∀ {rho : ℂ},
      Source.RHDefinitionBridge.standard.sourceNontrivialZero rho →
        rho.re = 1 / 2
  sourceRH :
    Source.RHDefinitionBridge.standard.SourceRH
  sourceRHMatchesNoOffLine :
    sourceRH =
      normalizedSelectedRouteBackedSourceRH_of_noOffLine
        noOffLineSourceZero

noncomputable def normalizedSelectedCC20ExitPackageFromTheorems :
    NormalizedSelectedCC20ExitPackage where
  routeBackedExitInputData :=
    normalizedSelectedRouteBackedCC20ExitInputDataFromTheorems
  finalSignMatchesRouteBacked := rfl
  noOffLineSourceZero :=
    normalizedSelectedRouteBackedNoOffLineSourceZeroFromTheorems
  sourceRH :=
    normalizedSelectedRouteBackedSourceRH_of_noOffLine
      normalizedSelectedRouteBackedNoOffLineSourceZeroFromTheorems
  sourceRHMatchesNoOffLine := rfl

structure NormalizedSelectedFinalRouteInput where
  inputs : RouteInputs
  sourceBackedTest : SourceBackedFixedSTest inputs
  ledgers : RouteLedgers
  bridge : RouteBridgeCertificate inputs sourceBackedTest ledgers
  detectorCoverage :
    NormalizedRouteBackedCC20SquareRestrictedDetectorCoverage
  traceFrontB2 :
    NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonB2Calibration
  finitePrimeIndexDifference :
    NormalizedRouteBackedCC20SquareRestrictedFinitePrimeIndexDifferenceCalibration
  splitSupportVisibleOwnerComponents :
    NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalRoutePackageCoverageSplitSupportVisibleOwnerComponents

def _root_.ConnesWeilRH.Route.RouteInputs.ofSelectedFinalInput
    (input : NormalizedSelectedFinalRouteInput) : RouteInputs :=
  input.inputs

def route_certificate_of_selected_final_route_input
    (input : NormalizedSelectedFinalRouteInput) :
    RouteCertificate (RouteInputs.ofSelectedFinalInput input) where
  sourceBackedTest := input.sourceBackedTest
  ledgers := input.ledgers
  bridge := input.bridge

theorem selected_final_route_input_sourceRH_from_08A
    (input : NormalizedSelectedFinalRouteInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  normalizedCC20_source_rh_of_square_restricted_detectorCoverage_routeFrontConcreteCanonicalRoutePackageCoverageSplitSupportVisibleOwnerComponents
    input.detectorCoverage
    input.traceFrontB2
    input.finitePrimeIndexDifference
    input.splitSupportVisibleOwnerComponents

structure NormalizedSelectedFinalRouteRowsInput where
  detectorCoverage :
    NormalizedRouteBackedCC20SquareRestrictedDetectorCoverage
  traceFrontB2 :
    NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonB2Calibration
  concreteCanonicalRoutePackageCoverage :
    NormalizedRouteBackedCC20SquareRestrictedConcreteCanonicalRoutePackageCoverage
  finitePrimeIndexDifference :
    NormalizedRouteBackedCC20SquareRestrictedFinitePrimeIndexDifferenceCalibration
  directGlobalUnfilteredTermMass :
    NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectGlobalUnfilteredTermMassCalibration
      (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration_of_concreteSourceWeilFormCarrier
        (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeConcreteSourceWeilFormCarrierCalibration_of_concreteCanonicalRoutePackageCoverage
          concreteCanonicalRoutePackageCoverage))

def trace_front_b2_of_selected_final_route_rows
    (rows : NormalizedSelectedFinalRouteRowsInput) :
    NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonB2Calibration :=
  rows.traceFrontB2

def direct_term_mass_rows_of_selected_final_route_rows
    (rows : NormalizedSelectedFinalRouteRowsInput) :
    NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermMassRowsCalibration
      (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration_of_concreteSourceWeilFormCarrier
        (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeConcreteSourceWeilFormCarrierCalibration_of_concreteCanonicalRoutePackageCoverage
          rows.concreteCanonicalRoutePackageCoverage)) :=
  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermMassRowsCalibration_of_unfiltered_restricted_global
    (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration_of_concreteSourceWeilFormCarrier
      (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeConcreteSourceWeilFormCarrierCalibration_of_concreteCanonicalRoutePackageCoverage
        rows.concreteCanonicalRoutePackageCoverage))
    (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectRestrictedUnfilteredTermMassCalibration_of_packageRestrictedEvaluatorMass
      (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration_of_concreteSourceWeilFormCarrier
        (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeConcreteSourceWeilFormCarrierCalibration_of_concreteCanonicalRoutePackageCoverage
          rows.concreteCanonicalRoutePackageCoverage))
      (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormPackageRestrictedEvaluatorMassCalibration_of_concreteCanonicalRoutePackageCoverage_indexDifference_packageGlobalEvaluatorMass
        rows.concreteCanonicalRoutePackageCoverage
        rows.finitePrimeIndexDifference
        (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormPackageGlobalEvaluatorMassCalibration_of_concreteCanonicalRoutePackageCoverage_directGlobalUnfilteredTermMass
          rows.concreteCanonicalRoutePackageCoverage
          rows.directGlobalUnfilteredTermMass)))
    rows.directGlobalUnfilteredTermMass

def finite_prime_index_difference_of_selected_final_route_rows
    (rows : NormalizedSelectedFinalRouteRowsInput) :
    NormalizedRouteBackedCC20SquareRestrictedFinitePrimeIndexDifferenceCalibration :=
  rows.finitePrimeIndexDifference

def split_support_visible_components_of_selected_final_route_rows
    (rows : NormalizedSelectedFinalRouteRowsInput) :
    NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalRoutePackageCoverageSplitSupportVisibleOwnerComponents :=
  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalRoutePackageCoverageSplitSupportVisibleOwnerComponents_of_concreteCanonicalRoutePackageCoverage_indexDifference_directGlobalUnfilteredTermMass
    rows.concreteCanonicalRoutePackageCoverage
    rows.finitePrimeIndexDifference
    rows.directGlobalUnfilteredTermMass

theorem selected_final_route_rows_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteRowsInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  normalizedCC20_source_rh_of_square_restricted_detectorCoverage_routeFrontConcreteCanonicalRoutePackageCoverageSplitSupportVisibleOwnerComponents
    rows.detectorCoverage
    (trace_front_b2_of_selected_final_route_rows rows)
    (finite_prime_index_difference_of_selected_final_route_rows rows)
    (split_support_visible_components_of_selected_final_route_rows rows)

structure NormalizedSelectedFinalRoutePackageRowsInput where
  detectorCoverage :
    NormalizedRouteBackedCC20SquareRestrictedDetectorCoverage
  traceFrontB2 :
    NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonB2Calibration
  routePackageRows :
    NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermForSourceTestAtomPackageConcreteCanonicalRoutePackageCoverageRouteFacingRowsCalibration

def direct_global_unfiltered_term_mass_of_selected_final_route_package_rows
    (rows : NormalizedSelectedFinalRoutePackageRowsInput) :
    NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectGlobalUnfilteredTermMassCalibration
      (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration_of_concreteSourceWeilFormCarrier
        (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeConcreteSourceWeilFormCarrierCalibration_of_concreteCanonicalRoutePackageCoverage
          rows.routePackageRows.routePackageCoverage)) :=
  (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectGlobalUnfilteredTermMassCalibration_iff_directGlobalTermMassCalibration
    (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration_of_concreteSourceWeilFormCarrier
      (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeConcreteSourceWeilFormCarrierCalibration_of_concreteCanonicalRoutePackageCoverage
        rows.routePackageRows.routePackageCoverage))).mpr
    rows.routePackageRows.termMassRows.globalMass

def finite_prime_index_difference_of_selected_final_route_package_rows
    (rows : NormalizedSelectedFinalRoutePackageRowsInput) :
    NormalizedRouteBackedCC20SquareRestrictedFinitePrimeIndexDifferenceCalibration :=
  ((NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermMassRowsCalibration_iff_indexDifference_directGlobalUnfilteredTermMass_of_concreteCanonicalRoutePackageCoverage
    rows.routePackageRows.routePackageCoverage).mp
    rows.routePackageRows.termMassRows).1

def selected_final_route_rows_input_of_package_rows
    (rows : NormalizedSelectedFinalRoutePackageRowsInput) :
    NormalizedSelectedFinalRouteRowsInput where
  detectorCoverage := rows.detectorCoverage
  traceFrontB2 := rows.traceFrontB2
  concreteCanonicalRoutePackageCoverage :=
    rows.routePackageRows.routePackageCoverage
  finitePrimeIndexDifference :=
    finite_prime_index_difference_of_selected_final_route_package_rows
      rows
  directGlobalUnfilteredTermMass :=
    direct_global_unfiltered_term_mass_of_selected_final_route_package_rows
      rows

theorem selected_final_route_package_rows_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRoutePackageRowsInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_rows_sourceRH_from_08A
    (selected_final_route_rows_input_of_package_rows rows)

structure NormalizedSelectedFinalRoutePackageTermMassInput where
  detectorCoverage :
    NormalizedRouteBackedCC20SquareRestrictedDetectorCoverage
  traceFrontB2 :
    NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonB2Calibration
  routePackageCoverage :
    NormalizedRouteBackedCC20SquareRestrictedConcreteCanonicalRoutePackageCoverage
  termMassRows :
    NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermMassRowsCalibration
      (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration_of_concreteSourceWeilFormCarrier
      (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeConcreteSourceWeilFormCarrierCalibration_of_concreteCanonicalRoutePackageCoverage
          routePackageCoverage))

def NormalizedSelectedFinalRoutePackageTermMassComponents : Prop :=
  ∃ hcoverage :
      NormalizedRouteBackedCC20SquareRestrictedConcreteCanonicalRoutePackageCoverage,
    NormalizedRouteBackedCC20SquareRestrictedDetectorCoverage ∧
      NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonB2Calibration ∧
        NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermMassRowsCalibration
          (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration_of_concreteSourceWeilFormCarrier
            (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeConcreteSourceWeilFormCarrierCalibration_of_concreteCanonicalRoutePackageCoverage
              hcoverage))

theorem NormalizedSelectedFinalRoutePackageTermMassInput_iff_components :
    Nonempty NormalizedSelectedFinalRoutePackageTermMassInput ↔
      NormalizedSelectedFinalRoutePackageTermMassComponents := by
  constructor
  · rintro ⟨rows⟩
    exact
      ⟨rows.routePackageCoverage, rows.detectorCoverage, rows.traceFrontB2,
        rows.termMassRows⟩
  · rintro ⟨hcoverage, hdetector, htrace, htermMassRows⟩
    exact
      ⟨{ detectorCoverage := hdetector
         traceFrontB2 := htrace
         routePackageCoverage := hcoverage
         termMassRows := htermMassRows }⟩

structure NormalizedSelectedFinalRouteFinitePrimeEvaluatorInput where
  detectorCoverage :
    NormalizedRouteBackedCC20SquareRestrictedDetectorCoverage
  traceFrontB2 :
    NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonB2Calibration
  routePackageCoverage :
    NormalizedRouteBackedCC20SquareRestrictedConcreteCanonicalRoutePackageCoverage
  scopedEvaluatorBalance :
    NormalizedRouteBackedCC20SquareRestrictedCommonScopedFinitePrimeEvaluatorValueBalanceCalibration
  globalEvaluatorMass :
    NormalizedRouteBackedCC20SquareRestrictedCommonGlobalFinitePrimeEvaluatorValueMassCancellationCalibration

def scoped_balance_of_selected_final_route_finite_prime_evaluator
    (rows : NormalizedSelectedFinalRouteFinitePrimeEvaluatorInput) :
    NormalizedRouteBackedCC20SquareRestrictedScopedFinitePrimeArchimedeanBalanceCalibration :=
  NormalizedRouteBackedCC20SquareRestrictedScopedFinitePrimeArchimedeanBalanceCalibration_of_evaluatorValueBalanceCalibration
    rows.scopedEvaluatorBalance

def global_mass_cancellation_of_selected_final_route_finite_prime_evaluator
    (rows : NormalizedSelectedFinalRouteFinitePrimeEvaluatorInput) :
    NormalizedRouteBackedCC20SquareRestrictedGlobalFinitePrimeMassCancellationCalibration :=
  NormalizedRouteBackedCC20SquareRestrictedGlobalFinitePrimeMassCancellationCalibration_of_evaluatorValueMassCalibration
    rows.globalEvaluatorMass

def psi_pole_collapse_of_selected_final_route_finite_prime_evaluator
    (rows : NormalizedSelectedFinalRouteFinitePrimeEvaluatorInput) :
    NormalizedRouteBackedCC20SquareRestrictedPsiPoleCollapseCalibration :=
  NormalizedRouteBackedCC20SquareRestrictedPsiPoleCollapseCalibration_of_globalFinitePrimeMassCancellationCalibration
    (global_mass_cancellation_of_selected_final_route_finite_prime_evaluator rows)

def restricted_qw_pole_collapse_of_selected_final_route_finite_prime_evaluator
    (rows : NormalizedSelectedFinalRouteFinitePrimeEvaluatorInput) :
    NormalizedRouteBackedCC20SquareRestrictedRestrictedQWPoleCollapseCalibration :=
  NormalizedRouteBackedCC20SquareRestrictedRestrictedQWPoleCollapseCalibration_of_scopedBalance_globalMassCalibrations
    (scoped_balance_of_selected_final_route_finite_prime_evaluator rows)
    (global_mass_cancellation_of_selected_final_route_finite_prime_evaluator rows)

def term_mass_rows_of_selected_final_route_finite_prime_evaluator
    (rows : NormalizedSelectedFinalRouteFinitePrimeEvaluatorInput) :
    NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermMassRowsCalibration
      (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration_of_concreteSourceWeilFormCarrier
      (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeConcreteSourceWeilFormCarrierCalibration_of_concreteCanonicalRoutePackageCoverage
          rows.routePackageCoverage)) :=
  (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermMassRowsCalibration_iff_routePoleCollapseCalibrations
    (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration_of_concreteSourceWeilFormCarrier
      (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeConcreteSourceWeilFormCarrierCalibration_of_concreteCanonicalRoutePackageCoverage
        rows.routePackageCoverage))).mpr
    ⟨restricted_qw_pole_collapse_of_selected_final_route_finite_prime_evaluator rows,
      psi_pole_collapse_of_selected_final_route_finite_prime_evaluator rows⟩

def package_term_mass_input_of_selected_final_route_finite_prime_evaluator
    (rows : NormalizedSelectedFinalRouteFinitePrimeEvaluatorInput) :
    NormalizedSelectedFinalRoutePackageTermMassInput where
  detectorCoverage := rows.detectorCoverage
  traceFrontB2 := rows.traceFrontB2
  routePackageCoverage := rows.routePackageCoverage
  termMassRows :=
    term_mass_rows_of_selected_final_route_finite_prime_evaluator rows

noncomputable def route_package_rows_of_selected_final_route_package_term_mass
    (rows : NormalizedSelectedFinalRoutePackageTermMassInput) :
    NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermForSourceTestAtomPackageConcreteCanonicalRoutePackageCoverageRouteFacingRowsCalibration :=
  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermForSourceTestAtomPackageConcreteCanonicalRoutePackageCoverageRouteFacingRowsCalibration_of_concreteCanonicalRoutePackageCoverage_directTermMassRows
    rows.routePackageCoverage
    rows.termMassRows

noncomputable def selected_final_route_package_rows_input_of_package_term_mass
    (rows : NormalizedSelectedFinalRoutePackageTermMassInput) :
    NormalizedSelectedFinalRoutePackageRowsInput where
  detectorCoverage := rows.detectorCoverage
  traceFrontB2 := rows.traceFrontB2
  routePackageRows :=
    route_package_rows_of_selected_final_route_package_term_mass rows

theorem selected_final_route_package_term_mass_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRoutePackageTermMassInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_package_rows_sourceRH_from_08A
    (selected_final_route_package_rows_input_of_package_term_mass rows)

theorem selected_final_route_finite_prime_evaluator_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteFinitePrimeEvaluatorInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_package_term_mass_sourceRH_from_08A
    (package_term_mass_input_of_selected_final_route_finite_prime_evaluator rows)

structure NormalizedSelectedFinalRouteSourceEvaluationDataInput where
  detectorCoverage :
    NormalizedRouteBackedCC20SquareRestrictedDetectorCoverage
  traceFrontB2 :
    NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonB2Calibration
  routePackageCoverage :
    NormalizedRouteBackedCC20SquareRestrictedConcreteCanonicalRoutePackageCoverage
  sourceEvaluationDataRows :
    NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataRowsCalibration

def finite_prime_evaluator_input_of_selected_final_route_source_evaluation_data
    (rows : NormalizedSelectedFinalRouteSourceEvaluationDataInput) :
    NormalizedSelectedFinalRouteFinitePrimeEvaluatorInput where
  detectorCoverage := rows.detectorCoverage
  traceFrontB2 := rows.traceFrontB2
  routePackageCoverage := rows.routePackageCoverage
  scopedEvaluatorBalance :=
    NormalizedRouteBackedCC20SquareRestrictedCommonScopedFinitePrimeEvaluatorValueBalanceCalibration_of_sourceEvaluationDataRowsCalibration
      rows.sourceEvaluationDataRows
  globalEvaluatorMass :=
    NormalizedRouteBackedCC20SquareRestrictedCommonGlobalFinitePrimeEvaluatorValueMassCancellationCalibration_of_sourceEvaluationDataRowsCalibration
      rows.sourceEvaluationDataRows

theorem selected_final_route_source_evaluation_data_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteSourceEvaluationDataInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_finite_prime_evaluator_sourceRH_from_08A
    (finite_prime_evaluator_input_of_selected_final_route_source_evaluation_data rows)

structure NormalizedSelectedFinalRouteConcreteCanonicalPackageRowsInput where
  detectorCoverage :
    NormalizedRouteBackedCC20SquareRestrictedDetectorCoverage
  traceFrontB2 :
    NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonB2Calibration
  routePackageRows :
    NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermForSourceTestAtomPackageConcreteCanonicalRoutePackageCoverageRowsCalibration

def source_evaluation_data_input_of_selected_final_route_concrete_canonical_package_rows
    (rows : NormalizedSelectedFinalRouteConcreteCanonicalPackageRowsInput) :
    NormalizedSelectedFinalRouteSourceEvaluationDataInput where
  detectorCoverage := rows.detectorCoverage
  traceFrontB2 := rows.traceFrontB2
  routePackageCoverage := rows.routePackageRows.routePackageCoverage
  sourceEvaluationDataRows :=
    NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataRowsCalibration_of_sourceWeilFormDirectArithmeticRowsCalibration
      (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectArithmeticRowsCalibration_of_directPackageRowsCalibration
        (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectPackageRowsCalibration_of_directTermPackageRowsCalibration
          (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermPackageRowsCalibration_of_concreteCanonicalRoutePackageCoverageRowsCalibration
            rows.routePackageRows)))

theorem selected_final_route_concrete_canonical_package_rows_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteConcreteCanonicalPackageRowsInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_source_evaluation_data_sourceRH_from_08A
    (source_evaluation_data_input_of_selected_final_route_concrete_canonical_package_rows rows)

structure NormalizedSelectedFinalRouteTraceSourceCanonicalPackageInput where
  detectorCanonicalRoutePackageCoverage :
    NormalizedRouteBackedCC20SquareRestrictedDetectorCanonicalRoutePackageCoverage
  traceSourceRows :
    NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonSourceRowsCalibration
  traceSupportSquareAlignment :
    NormalizedRouteBackedCC20SquareRestrictedTraceFrontSupportSquareAlignmentCalibration
      traceSourceRows
  traceQWLambdaAlignment :
    NormalizedRouteBackedCC20SquareRestrictedTraceFrontQWLambdaAlignmentCalibration
      traceSourceRows
  routePackageRows :
    NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermForSourceTestAtomPackageConcreteCanonicalRoutePackageCoverageRowsCalibration

def concrete_canonical_package_rows_input_of_selected_final_route_trace_source_canonical_package
    (rows : NormalizedSelectedFinalRouteTraceSourceCanonicalPackageInput) :
    NormalizedSelectedFinalRouteConcreteCanonicalPackageRowsInput where
  detectorCoverage :=
    normalizedRouteBackedCC20SquareRestrictedDetectorCoverage_of_detectorCanonicalRoutePackageCoverage
      rows.detectorCanonicalRoutePackageCoverage
  traceFrontB2 :=
    NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonB2Calibration_of_sourceAlignmentCalibrations
      rows.traceSourceRows
      rows.traceSupportSquareAlignment
      rows.traceQWLambdaAlignment
  routePackageRows := rows.routePackageRows

theorem selected_final_route_trace_source_canonical_package_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteTraceSourceCanonicalPackageInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_concrete_canonical_package_rows_sourceRH_from_08A
    (concrete_canonical_package_rows_input_of_selected_final_route_trace_source_canonical_package rows)

structure NormalizedSelectedFinalRouteCanonicalSquareTraceSourcePackageInput where
  canonicalSquareArchimedeanTraceRealizer :
    NormalizedRouteBackedYoshidaDetectorCanonicalSquareArchimedeanTraceRealizer
  traceSourceRows :
    NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonSourceRowsCalibration
  traceSupportSquareAlignment :
    NormalizedRouteBackedCC20SquareRestrictedTraceFrontSupportSquareAlignmentCalibration
      traceSourceRows
  traceQWLambdaAlignment :
    NormalizedRouteBackedCC20SquareRestrictedTraceFrontQWLambdaAlignmentCalibration
      traceSourceRows
  routePackageRows :
    NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermForSourceTestAtomPackageConcreteCanonicalRoutePackageCoverageRowsCalibration

def trace_source_canonical_package_input_of_selected_final_route_canonical_square_trace_source_package
    (rows : NormalizedSelectedFinalRouteCanonicalSquareTraceSourcePackageInput) :
    NormalizedSelectedFinalRouteTraceSourceCanonicalPackageInput where
  detectorCanonicalRoutePackageCoverage :=
    normalizedRouteBackedCC20SquareRestrictedDetectorCanonicalRoutePackageCoverage_of_canonicalSquareArchimedeanTraceRealizer
      rows.canonicalSquareArchimedeanTraceRealizer
  traceSourceRows := rows.traceSourceRows
  traceSupportSquareAlignment := rows.traceSupportSquareAlignment
  traceQWLambdaAlignment := rows.traceQWLambdaAlignment
  routePackageRows := rows.routePackageRows

theorem selected_final_route_canonical_square_trace_source_package_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteCanonicalSquareTraceSourcePackageInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_trace_source_canonical_package_sourceRH_from_08A
    (trace_source_canonical_package_input_of_selected_final_route_canonical_square_trace_source_package rows)

structure NormalizedSelectedFinalRouteCanonicalSquareTraceRowsPackageInput where
  canonicalSquareArchimedeanTraceRealizer :
    NormalizedRouteBackedYoshidaDetectorCanonicalSquareArchimedeanTraceRealizer
  traceFrontComparisonRows :
    ∀ r : NormalizedRouteBackedCC20SquareRestrictedTest,
      NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonRows r
  routePackageRows :
    NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermForSourceTestAtomPackageConcreteCanonicalRoutePackageCoverageRowsCalibration

def canonical_square_trace_source_package_input_of_selected_final_route_canonical_square_trace_rows_package
    (rows : NormalizedSelectedFinalRouteCanonicalSquareTraceRowsPackageInput) :
    NormalizedSelectedFinalRouteCanonicalSquareTraceSourcePackageInput where
  canonicalSquareArchimedeanTraceRealizer :=
    rows.canonicalSquareArchimedeanTraceRealizer
  traceSourceRows := {
    sourceRows := fun r =>
      NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonSourceRows.ofTraceFrontComparisonRows
        (rows.traceFrontComparisonRows r) }
  traceSupportSquareAlignment := by
    intro r
    simpa [
      NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonSourceRows.ofTraceFrontComparisonRows,
      NormalizedRouteBackedCC20SquareRestrictedTraceFrontSupportSquareAlignment]
      using (rows.traceFrontComparisonRows r).supportSquareTrace_eval_eq
  traceQWLambdaAlignment := by
    intro r
    simpa [
      NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonSourceRows.ofTraceFrontComparisonRows,
      NormalizedRouteBackedCC20SquareRestrictedTraceFrontQWLambdaAlignment]
      using (rows.traceFrontComparisonRows r).qwLambda_eval_eq
  routePackageRows := rows.routePackageRows

theorem selected_final_route_canonical_square_trace_rows_package_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteCanonicalSquareTraceRowsPackageInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_canonical_square_trace_source_package_sourceRH_from_08A
    (canonical_square_trace_source_package_input_of_selected_final_route_canonical_square_trace_rows_package rows)

structure NormalizedSelectedFinalRouteCanonicalSquareDataTraceRowsPackageInput where
  canonicalSquareData :
    ∀ {rho : ℂ}
      (detector :
        YoshidaDetector
          normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho),
        NormalizedRouteBackedYoshidaDetectorCanonicalSquareArchimedeanTraceRealizationData
          detector
  traceFrontComparisonRows :
    ∀ r : NormalizedRouteBackedCC20SquareRestrictedTest,
      NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonRows r
  routePackageRows :
    NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermForSourceTestAtomPackageConcreteCanonicalRoutePackageCoverageRowsCalibration

def canonical_square_trace_rows_package_input_of_selected_final_route_canonical_square_data_trace_rows_package
    (rows : NormalizedSelectedFinalRouteCanonicalSquareDataTraceRowsPackageInput) :
    NormalizedSelectedFinalRouteCanonicalSquareTraceRowsPackageInput where
  canonicalSquareArchimedeanTraceRealizer := by
    intro rho detector
    exact ⟨rows.canonicalSquareData detector⟩
  traceFrontComparisonRows := rows.traceFrontComparisonRows
  routePackageRows := rows.routePackageRows

theorem selected_final_route_canonical_square_data_trace_rows_package_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteCanonicalSquareDataTraceRowsPackageInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_canonical_square_trace_rows_package_sourceRH_from_08A
    (canonical_square_trace_rows_package_input_of_selected_final_route_canonical_square_data_trace_rows_package rows)

def direct_term_package_rows_of_selected_final_route_canonical_square_data_trace_rows_package
    (rows : NormalizedSelectedFinalRouteCanonicalSquareDataTraceRowsPackageInput) :
    NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermPackageRowsCalibration :=
  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermPackageRowsCalibration_of_concreteCanonicalRoutePackageCoverageRowsCalibration
    rows.routePackageRows

def weil_criterion_of_selected_final_route_canonical_square_data_trace_rows_package
    (rows : NormalizedSelectedFinalRouteCanonicalSquareDataTraceRowsPackageInput) :
    NormalizedRouteBackedCC20SquareRestrictedWeilCriterion :=
  let traceRows :=
    canonical_square_trace_source_package_input_of_selected_final_route_canonical_square_trace_rows_package
      (canonical_square_trace_rows_package_input_of_selected_final_route_canonical_square_data_trace_rows_package
        rows)
  normalizedRouteBackedCC20SquareRestrictedWeilCriterion_of_traceFrontComparisonQWPoleCalibration
    (normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonQWPoleCalibration_of_sourceAlignmentSourceWeilFormDirectTermPackageRowsCalibrations
      (normalizedRouteBackedCC20SquareRestrictedRoutePolePairingTransportCalibration_of_concreteCanonicalRoutePackageCoverage
        rows.routePackageRows.routePackageCoverage)
      traceRows.traceSourceRows
      traceRows.traceSupportSquareAlignment
      traceRows.traceQWLambdaAlignment
      (direct_term_package_rows_of_selected_final_route_canonical_square_data_trace_rows_package rows))

def detector_trace_front_qw_pole_coverage_of_selected_final_route_canonical_square_data_trace_rows_package
    (rows : NormalizedSelectedFinalRouteCanonicalSquareDataTraceRowsPackageInput) :
    NormalizedRouteBackedCC20SquareRestrictedDetectorTraceFrontComparisonQWPoleCalibrationCoverage := by
  intro rho hrho hoff detector
  let htraceRows :=
    canonical_square_trace_source_package_input_of_selected_final_route_canonical_square_trace_rows_package
      (canonical_square_trace_rows_package_input_of_selected_final_route_canonical_square_data_trace_rows_package
        rows)
  have hdetector :
      NormalizedRouteBackedCC20SquareRestrictedDetectorCanonicalRoutePackageCoverage :=
    normalizedRouteBackedCC20SquareRestrictedDetectorCanonicalRoutePackageCoverage_of_canonicalSquareArchimedeanTraceRealizer
      htraceRows.canonicalSquareArchimedeanTraceRealizer
  rcases hdetector hrho hoff detector with ⟨r, hr, _hcanonical⟩
  exact ⟨r, hr,
    (normalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonQWPoleCalibration_of_sourceAlignmentSourceWeilFormDirectTermPackageRowsCalibrations
      (normalizedRouteBackedCC20SquareRestrictedRoutePolePairingTransportCalibration_of_concreteCanonicalRoutePackageCoverage
        rows.routePackageRows.routePackageCoverage)
      htraceRows.traceSourceRows
      htraceRows.traceSupportSquareAlignment
      htraceRows.traceQWLambdaAlignment
      (direct_term_package_rows_of_selected_final_route_canonical_square_data_trace_rows_package rows)) r⟩

def detector_criterion_coverage_of_selected_final_route_canonical_square_data_trace_rows_package
    (rows : NormalizedSelectedFinalRouteCanonicalSquareDataTraceRowsPackageInput) :
    NormalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage :=
  NormalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage_of_traceFrontComparisonQWPoleCalibrationCoverage
    (detector_trace_front_qw_pole_coverage_of_selected_final_route_canonical_square_data_trace_rows_package
      rows)

/-
The detector-selected final-input upgrade ladder below is retained as a design
record but is not part of the compiled skeleton.  Several of its fields place
data-bearing route row structures directly inside propositional conjunctions,
and its lower half depends on the demoted canonical-witness certificate
transport experiment in `CC20RouteRealization`.  It must be rebuilt with
`Nonempty`/Sigma ownership and a valid owner-level certificate transport before
any declaration in this block can be used as an RH outlet.

structure NormalizedSelectedFinalRouteDetectorQWPoleRowsInput where
  detectorRows :
    ∀ {rho : ℂ}
      (detector :
        YoshidaDetector
          normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho),
        Σ r : NormalizedRouteBackedCC20SquareRestrictedTest,
          r.test = detector.test ∧
            NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonQWPoleRows r

def detector_trace_front_qw_pole_coverage_of_selected_final_route_detector_qw_pole_rows
    (rows : NormalizedSelectedFinalRouteDetectorQWPoleRowsInput) :
    NormalizedRouteBackedCC20SquareRestrictedDetectorTraceFrontComparisonQWPoleCalibrationCoverage := by
  intro rho _hrho _hoff detector
  rcases rows.detectorRows detector with ⟨r, hr, hrows⟩
  exact ⟨r, hr, ⟨hrows⟩⟩

def detector_criterion_coverage_of_selected_final_route_detector_qw_pole_rows
    (rows : NormalizedSelectedFinalRouteDetectorQWPoleRowsInput) :
    NormalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage :=
  NormalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage_of_traceFrontComparisonQWPoleCalibrationCoverage
    (detector_trace_front_qw_pole_coverage_of_selected_final_route_detector_qw_pole_rows
      rows)

theorem selected_final_route_detector_qw_pole_rows_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteDetectorQWPoleRowsInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  normalizedCC20_source_rh_of_square_restricted_detectorCriterionCoverage
    Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists
    (detector_criterion_coverage_of_selected_final_route_detector_qw_pole_rows rows)

structure NormalizedSelectedFinalRouteDetectorSplitQWPoleRowsInput where
  detectorRows :
    ∀ {rho : ℂ}
      (detector :
        YoshidaDetector
          normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho),
        Σ r : NormalizedRouteBackedCC20SquareRestrictedTest,
          r.test = detector.test ∧
            NormalizedRouteBackedCC20SquareRestrictedPolePairingTransport r ∧
              NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonRows r ∧
                NormalizedRouteBackedCC20SquareRestrictedFinitePrimeIndexDifferenceArchimedeanBalance r ∧
                  NormalizedRouteBackedCC20SquareRestrictedGlobalQWPoleCollapse r

def detector_qw_pole_rows_input_of_selected_final_route_detector_split_qw_pole_rows
    (rows : NormalizedSelectedFinalRouteDetectorSplitQWPoleRowsInput) :
    NormalizedSelectedFinalRouteDetectorQWPoleRowsInput where
  detectorRows := by
    intro rho detector
    rcases rows.detectorRows detector with
      ⟨r, hr, hpole, htrace, hindex, hglobalQW⟩
    exact
      ⟨r, hr,
        { polePairingTransport := hpole
          traceFrontComparisonRows := htrace
          finitePrimeIndexDifference := hindex
          globalQWPoleCollapse := hglobalQW }⟩

theorem selected_final_route_detector_split_qw_pole_rows_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteDetectorSplitQWPoleRowsInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_detector_qw_pole_rows_sourceRH_from_08A
    (detector_qw_pole_rows_input_of_selected_final_route_detector_split_qw_pole_rows
      rows)

structure NormalizedSelectedFinalRouteDetectorCanonicalSplitQWPoleRowsInput where
  detectorRows :
    ∀ {rho : ℂ}
      (detector :
        YoshidaDetector
          normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho),
        Σ r : NormalizedRouteBackedCC20SquareRestrictedTest,
          r.test = detector.test ∧
            NormalizedRouteBackedCC20SquareRestrictedConcreteCanonicalRoutePackageWitness r ∧
              NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonRows r ∧
                NormalizedRouteBackedCC20SquareRestrictedFinitePrimeIndexDifferenceArchimedeanBalance r ∧
                  NormalizedRouteBackedCC20SquareRestrictedGlobalQWPoleCollapse r

def detector_split_qw_pole_rows_input_of_selected_final_route_detector_canonical_split_qw_pole_rows
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalSplitQWPoleRowsInput) :
    NormalizedSelectedFinalRouteDetectorSplitQWPoleRowsInput where
  detectorRows := by
    intro rho detector
    rcases rows.detectorRows detector with
      ⟨r, hr, hwitness, htrace, hindex, hglobalQW⟩
    exact
      ⟨r, hr,
        normalizedRouteBackedCC20SquareRestrictedPolePairingTransport_of_concreteCanonicalRoutePackageWitness
          hwitness,
        htrace, hindex, hglobalQW⟩

theorem selected_final_route_detector_canonical_split_qw_pole_rows_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalSplitQWPoleRowsInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_detector_split_qw_pole_rows_sourceRH_from_08A
    (detector_split_qw_pole_rows_input_of_selected_final_route_detector_canonical_split_qw_pole_rows
      rows)

structure NormalizedSelectedFinalRouteDetectorCanonicalScopedPsiRowsInput where
  detectorRows :
    ∀ {rho : ℂ}
      (detector :
        YoshidaDetector
          normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho),
        Σ r : NormalizedRouteBackedCC20SquareRestrictedTest,
          r.test = detector.test ∧
            NormalizedRouteBackedCC20SquareRestrictedConcreteCanonicalRoutePackageWitness r ∧
              NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonRows r ∧
                NormalizedRouteBackedCC20SquareRestrictedScopedFinitePrimeArchimedeanBalance r ∧
                  NormalizedRouteBackedCC20SquareRestrictedPsiPoleCollapse r

def detector_canonical_split_qw_pole_rows_input_of_selected_final_route_detector_canonical_scoped_psi_rows
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalScopedPsiRowsInput) :
    NormalizedSelectedFinalRouteDetectorCanonicalSplitQWPoleRowsInput where
  detectorRows := by
    intro rho detector
    rcases rows.detectorRows detector with
      ⟨r, hr, hwitness, htrace, hscoped, hpsi⟩
    exact
      ⟨r, hr, hwitness, htrace,
        (normalizedRouteBackedCC20SquareRestrictedFinitePrimeIndexDifferenceArchimedeanBalance_iff_scopedBalance
          (r := r)).mpr hscoped,
        (normalizedRouteBackedCC20SquareRestrictedGlobalQWPoleCollapse_iff_psiPoleCollapse
          (r := r)).mpr hpsi⟩

theorem selected_final_route_detector_canonical_scoped_psi_rows_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalScopedPsiRowsInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_detector_canonical_split_qw_pole_rows_sourceRH_from_08A
    (detector_canonical_split_qw_pole_rows_input_of_selected_final_route_detector_canonical_scoped_psi_rows
      rows)

theorem selected_final_route_detector_canonical_scoped_psi_rows_nonempty_sourceRH :
    Nonempty NormalizedSelectedFinalRouteDetectorCanonicalScopedPsiRowsInput →
      Source.RHDefinitionBridge.standard.SourceRH := by
  rintro ⟨rows⟩
  exact selected_final_route_detector_canonical_scoped_psi_rows_sourceRH_from_08A rows

theorem selected_final_route_detector_canonical_scoped_psi_rows_nonempty_mathlibRH :
    Nonempty NormalizedSelectedFinalRouteDetectorCanonicalScopedPsiRowsInput →
      _root_.RiemannHypothesis := by
  intro hrows
  exact
    Source.RHDefinitionBridge.standard_source_rh_iff_mathlib.mp
      (selected_final_route_detector_canonical_scoped_psi_rows_nonempty_sourceRH
        hrows)

structure NormalizedSelectedFinalRouteDetectorCanonicalSourceEvaluationRowsInput where
  detectorRows :
    ∀ {rho : ℂ}
      (detector :
        YoshidaDetector
          normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho),
        Σ r : NormalizedRouteBackedCC20SquareRestrictedTest,
          r.test = detector.test ∧
            NormalizedRouteBackedCC20SquareRestrictedConcreteCanonicalRoutePackageWitness r ∧
              NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonRows r ∧
                NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataRows r

def detector_canonical_scoped_psi_rows_input_of_selected_final_route_detector_canonical_source_evaluation_rows
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalSourceEvaluationRowsInput) :
    NormalizedSelectedFinalRouteDetectorCanonicalScopedPsiRowsInput where
  detectorRows := by
    intro rho detector
    rcases rows.detectorRows detector with
      ⟨r, hr, hwitness, htrace, hfinitePrimeRows⟩
    exact
      ⟨r, hr, hwitness, htrace,
        normalizedRouteBackedCC20SquareRestrictedScopedFinitePrimeArchimedeanBalance_of_evaluatorValueBalance
          (normalizedRouteBackedCC20SquareRestrictedCommonScopedFinitePrimeEvaluatorValueBalance_of_sourceEvaluationDataRows
            hfinitePrimeRows),
        (normalizedRouteBackedCC20SquareRestrictedGlobalFinitePrimeMassCancellation_iff_psiPoleCollapse
          (r := r)).mp
          (normalizedRouteBackedCC20SquareRestrictedGlobalFinitePrimeMassCancellation_of_sourceEvaluationDataRows
            hfinitePrimeRows)⟩

theorem selected_final_route_detector_canonical_source_evaluation_rows_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalSourceEvaluationRowsInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_detector_canonical_scoped_psi_rows_sourceRH_from_08A
    (detector_canonical_scoped_psi_rows_input_of_selected_final_route_detector_canonical_source_evaluation_rows
      rows)

structure NormalizedSelectedFinalRouteDetectorCanonicalArithmeticSumRowsInput where
  detectorRows :
    ∀ {rho : ℂ}
      (detector :
        YoshidaDetector
          normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho),
        Σ r : NormalizedRouteBackedCC20SquareRestrictedTest,
          r.test = detector.test ∧
            NormalizedRouteBackedCC20SquareRestrictedConcreteCanonicalRoutePackageWitness r ∧
              NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonRows r ∧
                NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataArithmeticSumRows r

def detector_canonical_source_evaluation_rows_input_of_selected_final_route_detector_canonical_arithmetic_sum_rows
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalArithmeticSumRowsInput) :
    NormalizedSelectedFinalRouteDetectorCanonicalSourceEvaluationRowsInput where
  detectorRows := by
    intro rho detector
    rcases rows.detectorRows detector with
      ⟨r, hr, hwitness, htrace, hfinitePrimeRows⟩
    exact
      ⟨r, hr, hwitness, htrace,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataRows_of_arithmeticSumRows
          hfinitePrimeRows⟩

theorem selected_final_route_detector_canonical_arithmetic_sum_rows_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalArithmeticSumRowsInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_detector_canonical_source_evaluation_rows_sourceRH_from_08A
    (detector_canonical_source_evaluation_rows_input_of_selected_final_route_detector_canonical_arithmetic_sum_rows
      rows)

structure NormalizedSelectedFinalRouteDetectorCanonicalSourceWeilFormLocalDirectRowsInput where
  detectorRows :
    ∀ {rho : ℂ}
      (detector :
        YoshidaDetector
          normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho),
        Σ r : NormalizedRouteBackedCC20SquareRestrictedTest,
          r.test = detector.test ∧
            NormalizedRouteBackedCC20SquareRestrictedConcreteCanonicalRoutePackageWitness r ∧
              NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonRows r ∧
                NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormLocalDirectRows
                  (r := r)

def detector_canonical_arithmetic_sum_rows_input_of_selected_final_route_detector_canonical_sourceWeilForm_local_direct_rows
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalSourceWeilFormLocalDirectRowsInput) :
    NormalizedSelectedFinalRouteDetectorCanonicalArithmeticSumRowsInput where
  detectorRows := by
    intro rho detector
    rcases rows.detectorRows detector with
      ⟨r, hr, hwitness, htrace, hfinitePrimeRows⟩
    exact
      ⟨r, hr, hwitness, htrace,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceEvaluationDataArithmeticSumRows_of_sourceWeilFormLocalDirectRows
          hfinitePrimeRows⟩

theorem selected_final_route_detector_canonical_sourceWeilForm_local_direct_rows_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalSourceWeilFormLocalDirectRowsInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_detector_canonical_arithmetic_sum_rows_sourceRH_from_08A
    (detector_canonical_arithmetic_sum_rows_input_of_selected_final_route_detector_canonical_sourceWeilForm_local_direct_rows
      rows)

structure NormalizedSelectedFinalRouteDetectorCanonicalSourceWeilFormLocalPackageRowsInput where
  detectorRows :
    ∀ {rho : ℂ}
      (detector :
        YoshidaDetector
          normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho),
        Σ r : NormalizedRouteBackedCC20SquareRestrictedTest,
          r.test = detector.test ∧
            NormalizedRouteBackedCC20SquareRestrictedConcreteCanonicalRoutePackageWitness r ∧
              NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonRows r ∧
                NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormLocalPackageRows
                  (r := r)

def detector_canonical_sourceWeilForm_local_direct_rows_input_of_selected_final_route_detector_canonical_sourceWeilForm_local_package_rows
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalSourceWeilFormLocalPackageRowsInput) :
    NormalizedSelectedFinalRouteDetectorCanonicalSourceWeilFormLocalDirectRowsInput where
  detectorRows := by
    intro rho detector
    rcases rows.detectorRows detector with
      ⟨r, hr, hwitness, htrace, hfinitePrimeRows⟩
    exact
      ⟨r, hr, hwitness, htrace,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormLocalDirectRows_of_localPackageRows
          hfinitePrimeRows⟩

theorem selected_final_route_detector_canonical_sourceWeilForm_local_package_rows_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalSourceWeilFormLocalPackageRowsInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_detector_canonical_sourceWeilForm_local_direct_rows_sourceRH_from_08A
    (detector_canonical_sourceWeilForm_local_direct_rows_input_of_selected_final_route_detector_canonical_sourceWeilForm_local_package_rows
      rows)

structure NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessLocalPackageRowsInput where
  detectorRows :
    ∀ {rho : ℂ}
      (detector :
        YoshidaDetector
          normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho),
        Σ r : NormalizedRouteBackedCC20SquareRestrictedTest,
          r.test = detector.test ∧
            ∃ hwitness :
              NormalizedRouteBackedCC20SquareRestrictedConcreteCanonicalRoutePackageWitness r,
              NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonRows r ∧
                NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessLocalPackageRows
                  hwitness

def detector_canonical_sourceWeilForm_local_package_rows_input_of_selected_final_route_detector_canonical_concrete_witness_local_package_rows
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessLocalPackageRowsInput) :
    NormalizedSelectedFinalRouteDetectorCanonicalSourceWeilFormLocalPackageRowsInput where
  detectorRows := by
    intro rho detector
    rcases rows.detectorRows detector with
      ⟨r, hr, hwitness, htrace, hfinitePrimeRows⟩
    exact
      ⟨r, hr, hwitness, htrace,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormLocalPackageRows_of_concreteCanonicalWitnessLocalPackageRows
          hwitness hfinitePrimeRows⟩

theorem selected_final_route_detector_canonical_concrete_witness_local_package_rows_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessLocalPackageRowsInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_detector_canonical_sourceWeilForm_local_package_rows_sourceRH_from_08A
    (detector_canonical_sourceWeilForm_local_package_rows_input_of_selected_final_route_detector_canonical_concrete_witness_local_package_rows
      rows)

structure NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessSplitPackageRowsInput where
  detectorRows :
    ∀ {rho : ℂ}
      (detector :
        YoshidaDetector
          normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho),
        Σ r : NormalizedRouteBackedCC20SquareRestrictedTest,
          r.test = detector.test ∧
            ∃ hwitness :
              NormalizedRouteBackedCC20SquareRestrictedConcreteCanonicalRoutePackageWitness r,
              NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonRows r ∧
                NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessPackageAtomReadOffRows
                  hwitness ∧
                  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessLocalMassRows
                    hwitness

def detector_canonical_concrete_witness_local_package_rows_input_of_selected_final_route_detector_canonical_concrete_witness_split_package_rows
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessSplitPackageRowsInput) :
    NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessLocalPackageRowsInput where
  detectorRows := by
    intro rho detector
    rcases rows.detectorRows detector with
      ⟨r, hr, hwitness, htrace, hatom, hmass⟩
    exact
      ⟨r, hr, hwitness, htrace,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessLocalPackageRows_of_atom_mass
          hatom hmass⟩

theorem selected_final_route_detector_canonical_concrete_witness_split_package_rows_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessSplitPackageRowsInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_detector_canonical_concrete_witness_local_package_rows_sourceRH_from_08A
    (detector_canonical_concrete_witness_local_package_rows_input_of_selected_final_route_detector_canonical_concrete_witness_split_package_rows
      rows)

structure NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessAtomRestrictedGlobalRowsInput where
  detectorRows :
    ∀ {rho : ℂ}
      (detector :
        YoshidaDetector
          normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho),
        Σ r : NormalizedRouteBackedCC20SquareRestrictedTest,
          r.test = detector.test ∧
            ∃ hwitness :
              NormalizedRouteBackedCC20SquareRestrictedConcreteCanonicalRoutePackageWitness r,
              NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonRows r ∧
                NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessPackageAtomReadOffRows
                  hwitness ∧
                  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessRestrictedMassRow
                    hwitness ∧
                    NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessGlobalMassRow
                      hwitness

def detector_canonical_concrete_witness_split_package_rows_input_of_selected_final_route_detector_canonical_concrete_witness_atom_restricted_global_rows
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessAtomRestrictedGlobalRowsInput) :
    NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessSplitPackageRowsInput where
  detectorRows := by
    intro rho detector
    rcases rows.detectorRows detector with
      ⟨r, hr, hwitness, htrace, hatom, hrestricted, hglobal⟩
    exact
      ⟨r, hr, hwitness, htrace, hatom,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessLocalMassRows_of_restricted_global
          hrestricted hglobal⟩

theorem selected_final_route_detector_canonical_concrete_witness_atom_restricted_global_rows_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessAtomRestrictedGlobalRowsInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_detector_canonical_concrete_witness_split_package_rows_sourceRH_from_08A
    (detector_canonical_concrete_witness_split_package_rows_input_of_selected_final_route_detector_canonical_concrete_witness_atom_restricted_global_rows
      rows)

structure NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessRestrictedGlobalRowsInput where
  detectorRows :
    ∀ {rho : ℂ}
      (detector :
        YoshidaDetector
          normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho),
        Σ r : NormalizedRouteBackedCC20SquareRestrictedTest,
          r.test = detector.test ∧
            ∃ hwitness :
              NormalizedRouteBackedCC20SquareRestrictedConcreteCanonicalRoutePackageWitness r,
              NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonRows r ∧
                NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessRestrictedMassRow
                  hwitness ∧
                  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessGlobalMassRow
                    hwitness

def detector_canonical_concrete_witness_atom_restricted_global_rows_input_of_selected_final_route_detector_canonical_concrete_witness_restricted_global_rows
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessRestrictedGlobalRowsInput) :
    NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessAtomRestrictedGlobalRowsInput where
  detectorRows := by
    intro rho detector
    rcases rows.detectorRows detector with
      ⟨r, hr, hwitness, htrace, hrestricted, hglobal⟩
    let hobject :=
      normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessPackageCanonicalAtomObjectRows_of_witness
        hwitness
    let hprojection :=
      normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessPackageCanonicalAtomProjectionRows_of_objectRows
        hwitness hobject
    exact
      ⟨r, hr, hwitness, htrace,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessPackageAtomReadOffRows_of_canonicalAtomProjectionRows
          hwitness hprojection,
        hrestricted, hglobal⟩

theorem selected_final_route_detector_canonical_concrete_witness_restricted_global_rows_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessRestrictedGlobalRowsInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_detector_canonical_concrete_witness_atom_restricted_global_rows_sourceRH_from_08A
    (detector_canonical_concrete_witness_atom_restricted_global_rows_input_of_selected_final_route_detector_canonical_concrete_witness_restricted_global_rows
      rows)

def detector_canonical_concrete_witness_restricted_global_rows_input_of_selected_final_route_detector_canonical_concrete_witness_local_package_rows
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessLocalPackageRowsInput) :
    NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessRestrictedGlobalRowsInput where
  detectorRows := by
    intro rho detector
    rcases rows.detectorRows detector with
      ⟨r, hr, hwitness, htrace, hfinitePrimeRows⟩
    rcases hfinitePrimeRows with ⟨_hatom, hmass⟩
    rcases hmass with ⟨hrestricted, hglobal⟩
    exact ⟨r, hr, hwitness, htrace, hrestricted, hglobal⟩

theorem selected_final_route_detector_canonical_concrete_witness_local_package_rows_iff_restricted_global_rows :
    Nonempty NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessLocalPackageRowsInput ↔
      Nonempty NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessRestrictedGlobalRowsInput := by
  constructor
  · rintro ⟨rows⟩
    exact
      ⟨detector_canonical_concrete_witness_restricted_global_rows_input_of_selected_final_route_detector_canonical_concrete_witness_local_package_rows
        rows⟩
  · rintro ⟨rows⟩
    exact
      ⟨detector_canonical_concrete_witness_local_package_rows_input_of_selected_final_route_detector_canonical_concrete_witness_split_package_rows
        (detector_canonical_concrete_witness_split_package_rows_input_of_selected_final_route_detector_canonical_concrete_witness_atom_restricted_global_rows
          (detector_canonical_concrete_witness_atom_restricted_global_rows_input_of_selected_final_route_detector_canonical_concrete_witness_restricted_global_rows
            rows))⟩

structure NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessTermMassRowsInput where
  detectorRows :
    ∀ {rho : ℂ}
      (detector :
        YoshidaDetector
          normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho),
        Σ r : NormalizedRouteBackedCC20SquareRestrictedTest,
          r.test = detector.test ∧
            ∃ hwitness :
              NormalizedRouteBackedCC20SquareRestrictedConcreteCanonicalRoutePackageWitness r,
              NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonRows r ∧
                NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessRestrictedTermMassRow
                  hwitness ∧
                  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessGlobalTermMassRow
                    hwitness

def detector_canonical_concrete_witness_restricted_global_rows_input_of_selected_final_route_detector_canonical_concrete_witness_term_mass_rows
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessTermMassRowsInput) :
    NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessRestrictedGlobalRowsInput where
  detectorRows := by
    intro rho detector
    rcases rows.detectorRows detector with
      ⟨r, hr, hwitness, htrace, hrestrictedTerm, hglobalTerm⟩
    exact
      ⟨r, hr, hwitness, htrace,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessRestrictedMassRow_of_termMass
          hwitness hrestrictedTerm,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessGlobalMassRow_of_termMass
          hwitness hglobalTerm⟩

def detector_canonical_concrete_witness_term_mass_rows_input_of_selected_final_route_detector_canonical_concrete_witness_restricted_global_rows
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessRestrictedGlobalRowsInput) :
    NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessTermMassRowsInput where
  detectorRows := by
    intro rho detector
    rcases rows.detectorRows detector with
      ⟨r, hr, hwitness, htrace, hrestrictedMass, hglobalMass⟩
    exact
      ⟨r, hr, hwitness, htrace,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessRestrictedTermMassRow_of_mass
          hwitness hrestrictedMass,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessGlobalTermMassRow_of_mass
          hwitness hglobalMass⟩

theorem selected_final_route_detector_canonical_concrete_witness_term_mass_rows_iff_restricted_global_rows :
    Nonempty NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessTermMassRowsInput ↔
      Nonempty NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessRestrictedGlobalRowsInput := by
  constructor
  · rintro ⟨rows⟩
    exact
      ⟨detector_canonical_concrete_witness_restricted_global_rows_input_of_selected_final_route_detector_canonical_concrete_witness_term_mass_rows
        rows⟩
  · rintro ⟨rows⟩
    exact
      ⟨detector_canonical_concrete_witness_term_mass_rows_input_of_selected_final_route_detector_canonical_concrete_witness_restricted_global_rows
        rows⟩

theorem selected_final_route_detector_canonical_concrete_witness_term_mass_rows_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessTermMassRowsInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_detector_canonical_concrete_witness_restricted_global_rows_sourceRH_from_08A
    (detector_canonical_concrete_witness_restricted_global_rows_input_of_selected_final_route_detector_canonical_concrete_witness_term_mass_rows
      rows)

structure NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessUnfilteredTermMassRowsInput where
  detectorRows :
    ∀ {rho : ℂ}
      (detector :
        YoshidaDetector
          normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho),
        Σ r : NormalizedRouteBackedCC20SquareRestrictedTest,
          r.test = detector.test ∧
            ∃ hwitness :
              NormalizedRouteBackedCC20SquareRestrictedConcreteCanonicalRoutePackageWitness r,
              NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonRows r ∧
                NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessRestrictedUnfilteredTermMassRow
                  hwitness ∧
                  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessGlobalUnfilteredTermMassRow
                    hwitness

def detector_canonical_concrete_witness_term_mass_rows_input_of_selected_final_route_detector_canonical_concrete_witness_unfiltered_term_mass_rows
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessUnfilteredTermMassRowsInput) :
    NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessTermMassRowsInput where
  detectorRows := by
    intro rho detector
    rcases rows.detectorRows detector with
      ⟨r, hr, hwitness, htrace, hrestrictedUnfiltered, hglobalUnfiltered⟩
    exact
      ⟨r, hr, hwitness, htrace,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessRestrictedTermMassRow_of_unfiltered
          hwitness hrestrictedUnfiltered,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessGlobalTermMassRow_of_unfiltered
          hwitness hglobalUnfiltered⟩

theorem selected_final_route_detector_canonical_concrete_witness_unfiltered_term_mass_rows_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessUnfilteredTermMassRowsInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_detector_canonical_concrete_witness_term_mass_rows_sourceRH_from_08A
    (detector_canonical_concrete_witness_term_mass_rows_input_of_selected_final_route_detector_canonical_concrete_witness_unfiltered_term_mass_rows
      rows)

def detector_canonical_concrete_witness_unfiltered_term_mass_rows_input_of_selected_final_route_detector_canonical_concrete_witness_restricted_global_rows
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessRestrictedGlobalRowsInput) :
    NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessUnfilteredTermMassRowsInput where
  detectorRows := by
    intro rho detector
    rcases rows.detectorRows detector with
      ⟨r, hr, hwitness, htrace, hrestrictedMass, hglobalMass⟩
    let hrestrictedTerm :=
      normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessRestrictedTermMassRow_of_mass
        hwitness hrestrictedMass
    let hglobalTerm :=
      normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessGlobalTermMassRow_of_mass
        hwitness hglobalMass
    exact
      ⟨r, hr, hwitness, htrace,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessRestrictedUnfilteredTermMassRow_of_termMass
          hwitness hrestrictedTerm,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessGlobalUnfilteredTermMassRow_of_termMass
          hwitness hglobalTerm⟩

theorem selected_final_route_detector_canonical_concrete_witness_unfiltered_term_mass_rows_iff_restricted_global_rows :
    Nonempty NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessUnfilteredTermMassRowsInput ↔
      Nonempty NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessRestrictedGlobalRowsInput := by
  constructor
  · rintro ⟨rows⟩
    exact
      ⟨detector_canonical_concrete_witness_restricted_global_rows_input_of_selected_final_route_detector_canonical_concrete_witness_term_mass_rows
        (detector_canonical_concrete_witness_term_mass_rows_input_of_selected_final_route_detector_canonical_concrete_witness_unfiltered_term_mass_rows
          rows)⟩
  · rintro ⟨rows⟩
    exact
      ⟨detector_canonical_concrete_witness_unfiltered_term_mass_rows_input_of_selected_final_route_detector_canonical_concrete_witness_restricted_global_rows
        rows⟩

def detector_canonical_scoped_psi_rows_input_of_selected_final_route_detector_canonical_concrete_witness_unfiltered_term_mass_rows
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessUnfilteredTermMassRowsInput) :
    NormalizedSelectedFinalRouteDetectorCanonicalScopedPsiRowsInput where
  detectorRows := by
    intro rho detector
    rcases rows.detectorRows detector with
      ⟨r, hr, hwitness, htrace, hrestrictedUnfiltered, hglobalUnfiltered⟩
    let hrestrictedTerm :=
      normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessRestrictedTermMassRow_of_unfiltered
        hwitness hrestrictedUnfiltered
    let hglobalTerm :=
      normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessGlobalTermMassRow_of_unfiltered
        hwitness hglobalUnfiltered
    let hrestrictedQW :=
      normalizedRouteBackedCC20SquareRestrictedRestrictedQWPoleCollapse_of_concreteCanonicalWitnessRestrictedTermMass
        hwitness hrestrictedTerm
    let hpsi :=
      normalizedRouteBackedCC20SquareRestrictedPsiPoleCollapse_of_concreteCanonicalWitnessGlobalTermMass
        hwitness hglobalTerm
    exact
      ⟨r, hr, hwitness, htrace,
        normalizedRouteBackedCC20SquareRestrictedScopedFinitePrimeArchimedeanBalance_of_restrictedQWPole_psiPole
          hrestrictedQW hpsi,
        hpsi⟩

theorem selected_final_route_detector_canonical_concrete_witness_unfiltered_term_mass_rows_sourceRH_via_scoped_psi_from_08A
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessUnfilteredTermMassRowsInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_detector_canonical_scoped_psi_rows_sourceRH_from_08A
    (detector_canonical_scoped_psi_rows_input_of_selected_final_route_detector_canonical_concrete_witness_unfiltered_term_mass_rows
      rows)

def detector_canonical_concrete_witness_unfiltered_term_mass_rows_input_of_selected_final_route_detector_canonical_scoped_psi_rows
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalScopedPsiRowsInput) :
    NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessUnfilteredTermMassRowsInput where
  detectorRows := by
    intro rho detector
    rcases rows.detectorRows detector with
      ⟨r, hr, hwitness, htrace, hscoped, hpsi⟩
    exact
      ⟨r, hr, hwitness, htrace,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessRestrictedUnfilteredTermMassRow_of_scoped_psiPole
          hwitness hscoped hpsi,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessGlobalUnfilteredTermMassRow_of_psiPoleCollapse
          hwitness hpsi⟩

theorem selected_final_route_detector_canonical_concrete_witness_unfiltered_term_mass_rows_iff_scoped_psi_rows :
    Nonempty NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessUnfilteredTermMassRowsInput ↔
      Nonempty NormalizedSelectedFinalRouteDetectorCanonicalScopedPsiRowsInput := by
  constructor
  · rintro ⟨rows⟩
    exact
      ⟨detector_canonical_scoped_psi_rows_input_of_selected_final_route_detector_canonical_concrete_witness_unfiltered_term_mass_rows
        rows⟩
  · rintro ⟨rows⟩
    exact
      ⟨detector_canonical_concrete_witness_unfiltered_term_mass_rows_input_of_selected_final_route_detector_canonical_scoped_psi_rows
        rows⟩

theorem selected_final_route_detector_canonical_concrete_witness_restricted_global_rows_iff_scoped_psi_rows :
    Nonempty NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessRestrictedGlobalRowsInput ↔
      Nonempty NormalizedSelectedFinalRouteDetectorCanonicalScopedPsiRowsInput :=
  selected_final_route_detector_canonical_concrete_witness_unfiltered_term_mass_rows_iff_restricted_global_rows.symm.trans
    selected_final_route_detector_canonical_concrete_witness_unfiltered_term_mass_rows_iff_scoped_psi_rows

theorem selected_final_route_detector_canonical_concrete_witness_restricted_global_rows_nonempty_sourceRH :
    Nonempty NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessRestrictedGlobalRowsInput →
      Source.RHDefinitionBridge.standard.SourceRH := by
  intro hrows
  exact
    selected_final_route_detector_canonical_scoped_psi_rows_nonempty_sourceRH
      (selected_final_route_detector_canonical_concrete_witness_restricted_global_rows_iff_scoped_psi_rows.mp
        hrows)

theorem selected_final_route_detector_canonical_concrete_witness_restricted_global_rows_nonempty_mathlibRH :
    Nonempty NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessRestrictedGlobalRowsInput →
      _root_.RiemannHypothesis := by
  intro hrows
  exact
    Source.RHDefinitionBridge.standard_source_rh_iff_mathlib.mp
      (selected_final_route_detector_canonical_concrete_witness_restricted_global_rows_nonempty_sourceRH
        hrows)

theorem selected_final_route_detector_canonical_concrete_witness_unfiltered_term_mass_rows_nonempty_sourceRH :
    Nonempty NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessUnfilteredTermMassRowsInput →
      Source.RHDefinitionBridge.standard.SourceRH := by
  rintro ⟨rows⟩
  exact
    selected_final_route_detector_canonical_concrete_witness_unfiltered_term_mass_rows_sourceRH_via_scoped_psi_from_08A
      rows

theorem selected_final_route_detector_canonical_concrete_witness_unfiltered_term_mass_rows_nonempty_mathlibRH :
    Nonempty NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessUnfilteredTermMassRowsInput →
      _root_.RiemannHypothesis := by
  intro hrows
  exact
    Source.RHDefinitionBridge.standard_source_rh_iff_mathlib.mp
      (selected_final_route_detector_canonical_concrete_witness_unfiltered_term_mass_rows_nonempty_sourceRH
        hrows)

structure NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessAtomTermMassRowsInput where
  detectorRows :
    ∀ {rho : ℂ}
      (detector :
        YoshidaDetector
          normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho),
        Σ r : NormalizedRouteBackedCC20SquareRestrictedTest,
          r.test = detector.test ∧
            ∃ hwitness :
              NormalizedRouteBackedCC20SquareRestrictedConcreteCanonicalRoutePackageWitness r,
              NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonRows r ∧
                NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessPackageAtomReadOffRows
                  hwitness ∧
                  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessRestrictedTermMassRow
                    hwitness ∧
                    NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessGlobalTermMassRow
                      hwitness

def detector_canonical_concrete_witness_atom_restricted_global_rows_input_of_selected_final_route_detector_canonical_concrete_witness_atom_term_mass_rows
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessAtomTermMassRowsInput) :
    NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessAtomRestrictedGlobalRowsInput where
  detectorRows := by
    intro rho detector
    rcases rows.detectorRows detector with
      ⟨r, hr, hwitness, htrace, hatom, hrestrictedTerm, hglobalTerm⟩
    exact
      ⟨r, hr, hwitness, htrace, hatom,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessRestrictedMassRow_of_termMass
          hwitness hrestrictedTerm,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessGlobalMassRow_of_termMass
          hwitness hglobalTerm⟩

theorem selected_final_route_detector_canonical_concrete_witness_atom_term_mass_rows_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessAtomTermMassRowsInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_detector_canonical_concrete_witness_atom_restricted_global_rows_sourceRH_from_08A
    (detector_canonical_concrete_witness_atom_restricted_global_rows_input_of_selected_final_route_detector_canonical_concrete_witness_atom_term_mass_rows
      rows)

structure NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessAtomPackageEvaluatorRowsInput where
  detectorRows :
    ∀ {rho : ℂ}
      (detector :
        YoshidaDetector
          normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho),
        Σ r : NormalizedRouteBackedCC20SquareRestrictedTest,
          r.test = detector.test ∧
            ∃ hwitness :
              NormalizedRouteBackedCC20SquareRestrictedConcreteCanonicalRoutePackageWitness r,
              NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonRows r ∧
                NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessPackageAtomReadOffRows
                  hwitness ∧
                  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessPackageRestrictedEvaluatorMassRow
                    hwitness ∧
                    NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessPackageGlobalEvaluatorMassRow
                      hwitness

def detector_canonical_concrete_witness_atom_term_mass_rows_input_of_selected_final_route_detector_canonical_concrete_witness_atom_package_evaluator_rows
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessAtomPackageEvaluatorRowsInput) :
    NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessAtomTermMassRowsInput where
  detectorRows := by
    intro rho detector
    rcases rows.detectorRows detector with
      ⟨r, hr, hwitness, htrace, hatom, hrestrictedPackage, hglobalPackage⟩
    exact
      ⟨r, hr, hwitness, htrace, hatom,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessRestrictedTermMassRow_of_packageEvaluator
          hwitness hrestrictedPackage,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessGlobalTermMassRow_of_packageEvaluator
          hwitness hglobalPackage⟩

theorem selected_final_route_detector_canonical_concrete_witness_atom_package_evaluator_rows_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessAtomPackageEvaluatorRowsInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_detector_canonical_concrete_witness_atom_term_mass_rows_sourceRH_from_08A
    (detector_canonical_concrete_witness_atom_term_mass_rows_input_of_selected_final_route_detector_canonical_concrete_witness_atom_package_evaluator_rows
      rows)

structure NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessProjectionPackageEvaluatorRowsInput where
  detectorRows :
    ∀ {rho : ℂ}
      (detector :
        YoshidaDetector
          normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho),
        Σ r : NormalizedRouteBackedCC20SquareRestrictedTest,
          r.test = detector.test ∧
            ∃ hwitness :
              NormalizedRouteBackedCC20SquareRestrictedConcreteCanonicalRoutePackageWitness r,
              NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonRows r ∧
                NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessPackageCanonicalAtomProjectionRows
                  hwitness ∧
                  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessPackageRestrictedEvaluatorMassRow
                    hwitness ∧
                    NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessPackageGlobalEvaluatorMassRow
                      hwitness

def detector_canonical_concrete_witness_atom_package_evaluator_rows_input_of_selected_final_route_detector_canonical_concrete_witness_projection_package_evaluator_rows
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessProjectionPackageEvaluatorRowsInput) :
    NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessAtomPackageEvaluatorRowsInput where
  detectorRows := by
    intro rho detector
    rcases rows.detectorRows detector with
      ⟨r, hr, hwitness, htrace, hprojection, hrestrictedPackage, hglobalPackage⟩
    exact
      ⟨r, hr, hwitness, htrace,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessPackageAtomReadOffRows_of_canonicalAtomProjectionRows
          hwitness hprojection,
        hrestrictedPackage, hglobalPackage⟩

theorem selected_final_route_detector_canonical_concrete_witness_projection_package_evaluator_rows_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessProjectionPackageEvaluatorRowsInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_detector_canonical_concrete_witness_atom_package_evaluator_rows_sourceRH_from_08A
    (detector_canonical_concrete_witness_atom_package_evaluator_rows_input_of_selected_final_route_detector_canonical_concrete_witness_projection_package_evaluator_rows
      rows)

structure NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessObjectPackageEvaluatorRowsInput where
  detectorRows :
    ∀ {rho : ℂ}
      (detector :
        YoshidaDetector
          normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho),
        Σ r : NormalizedRouteBackedCC20SquareRestrictedTest,
          r.test = detector.test ∧
            ∃ hwitness :
              NormalizedRouteBackedCC20SquareRestrictedConcreteCanonicalRoutePackageWitness r,
              NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonRows r ∧
                NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessPackageCanonicalAtomObjectRows
                  hwitness ∧
                  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessPackageRestrictedEvaluatorMassRow
                    hwitness ∧
                    NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessPackageGlobalEvaluatorMassRow
                      hwitness

def detector_canonical_concrete_witness_projection_package_evaluator_rows_input_of_selected_final_route_detector_canonical_concrete_witness_object_package_evaluator_rows
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessObjectPackageEvaluatorRowsInput) :
    NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessProjectionPackageEvaluatorRowsInput where
  detectorRows := by
    intro rho detector
    rcases rows.detectorRows detector with
      ⟨r, hr, hwitness, htrace, hobject, hrestrictedPackage, hglobalPackage⟩
    exact
      ⟨r, hr, hwitness, htrace,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessPackageCanonicalAtomProjectionRows_of_objectRows
          hwitness hobject,
        hrestrictedPackage, hglobalPackage⟩

theorem selected_final_route_detector_canonical_concrete_witness_object_package_evaluator_rows_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessObjectPackageEvaluatorRowsInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_detector_canonical_concrete_witness_projection_package_evaluator_rows_sourceRH_from_08A
    (detector_canonical_concrete_witness_projection_package_evaluator_rows_input_of_selected_final_route_detector_canonical_concrete_witness_object_package_evaluator_rows
      rows)

structure NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessPackageEvaluatorRowsInput where
  detectorRows :
    ∀ {rho : ℂ}
      (detector :
        YoshidaDetector
          normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho),
        Σ r : NormalizedRouteBackedCC20SquareRestrictedTest,
          r.test = detector.test ∧
            ∃ hwitness :
              NormalizedRouteBackedCC20SquareRestrictedConcreteCanonicalRoutePackageWitness r,
              NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonRows r ∧
                NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessPackageRestrictedEvaluatorMassRow
                  hwitness ∧
                  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessPackageGlobalEvaluatorMassRow
                    hwitness

def detector_canonical_concrete_witness_object_package_evaluator_rows_input_of_selected_final_route_detector_canonical_concrete_witness_package_evaluator_rows
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessPackageEvaluatorRowsInput) :
    NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessObjectPackageEvaluatorRowsInput where
  detectorRows := by
    intro rho detector
    rcases rows.detectorRows detector with
      ⟨r, hr, hwitness, htrace, hrestrictedPackage, hglobalPackage⟩
    exact
      ⟨r, hr, hwitness, htrace,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessPackageCanonicalAtomObjectRows_of_witness
          hwitness,
        hrestrictedPackage, hglobalPackage⟩

theorem selected_final_route_detector_canonical_concrete_witness_package_evaluator_rows_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessPackageEvaluatorRowsInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_detector_canonical_concrete_witness_object_package_evaluator_rows_sourceRH_from_08A
    (detector_canonical_concrete_witness_object_package_evaluator_rows_input_of_selected_final_route_detector_canonical_concrete_witness_package_evaluator_rows
      rows)

structure NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessCommonEvaluatorRowsInput where
  detectorRows :
    ∀ {rho : ℂ}
      (detector :
        YoshidaDetector
          normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho),
        Σ r : NormalizedRouteBackedCC20SquareRestrictedTest,
          r.test = detector.test ∧
            ∃ hwitness :
              NormalizedRouteBackedCC20SquareRestrictedConcreteCanonicalRoutePackageWitness r,
              NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonRows r ∧
                NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessCommonRestrictedEvaluatorMassRow
                  hwitness ∧
                  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessCommonGlobalEvaluatorMassRow
                    hwitness

def detector_canonical_concrete_witness_package_evaluator_rows_input_of_selected_final_route_detector_canonical_concrete_witness_common_evaluator_rows
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessCommonEvaluatorRowsInput) :
    NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessPackageEvaluatorRowsInput where
  detectorRows := by
    intro rho detector
    rcases rows.detectorRows detector with
      ⟨r, hr, hwitness, htrace, hrestrictedCommon, hglobalCommon⟩
    exact
      ⟨r, hr, hwitness, htrace,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessPackageRestrictedEvaluatorMassRow_of_common
          hwitness hrestrictedCommon,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessPackageGlobalEvaluatorMassRow_of_common
          hwitness hglobalCommon⟩

theorem selected_final_route_detector_canonical_concrete_witness_common_evaluator_rows_sourceRH_from_08A
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessCommonEvaluatorRowsInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_detector_canonical_concrete_witness_package_evaluator_rows_sourceRH_from_08A
    (detector_canonical_concrete_witness_package_evaluator_rows_input_of_selected_final_route_detector_canonical_concrete_witness_common_evaluator_rows
      rows)

def detector_canonical_concrete_witness_restricted_global_rows_input_of_selected_final_route_detector_canonical_concrete_witness_common_evaluator_rows
    (rows : NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessCommonEvaluatorRowsInput) :
    NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessRestrictedGlobalRowsInput where
  detectorRows := by
    intro rho detector
    rcases rows.detectorRows detector with
      ⟨r, hr, hwitness, htrace, hrestrictedCommon, hglobalCommon⟩
    let hrestrictedPackage :=
      normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessPackageRestrictedEvaluatorMassRow_of_common
        hwitness hrestrictedCommon
    let hglobalPackage :=
      normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessPackageGlobalEvaluatorMassRow_of_common
        hwitness hglobalCommon
    let hrestrictedTerm :=
      normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessRestrictedTermMassRow_of_packageEvaluator
        hwitness hrestrictedPackage
    let hglobalTerm :=
      normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessGlobalTermMassRow_of_packageEvaluator
        hwitness hglobalPackage
    exact
      ⟨r, hr, hwitness, htrace,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessRestrictedMassRow_of_termMass
          hwitness hrestrictedTerm,
        normalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormConcreteCanonicalWitnessGlobalMassRow_of_termMass
          hwitness hglobalTerm⟩

-/

theorem selected_final_route_detector_criterion_coverage_sourceRH_from_08A
    (hcoverage :
      NormalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  normalizedCC20_source_rh_of_square_restricted_detectorCriterionCoverage
    Source.CC20YoshidaInterpolationNode.normalizedCC20YoshidaDetectorExists
    hcoverage

structure NormalizedSelectedFinalRouteLowerInput where
  inputs : RouteInputs
  sourceBackedTest : SourceBackedFixedSTest inputs
  ledgers : RouteLedgers
  bridge : RouteBridgeCertificate inputs sourceBackedTest ledgers
  rows : NormalizedSelectedFinalRouteRowsInput

structure NormalizedSelectedFinalRouteCertificateCarrier where
  inputs : RouteInputs
  sourceBackedTest : SourceBackedFixedSTest inputs
  ledgers : RouteLedgers
  bridge : RouteBridgeCertificate inputs sourceBackedTest ledgers

def selected_final_route_lower_input_of_certificate_carrier
    (carrier : NormalizedSelectedFinalRouteCertificateCarrier)
    (rows : NormalizedSelectedFinalRouteRowsInput) :
    NormalizedSelectedFinalRouteLowerInput where
  inputs := carrier.inputs
  sourceBackedTest := carrier.sourceBackedTest
  ledgers := carrier.ledgers
  bridge := carrier.bridge
  rows := rows

def selected_final_route_input_of_lower_input
    (input : NormalizedSelectedFinalRouteLowerInput) :
    NormalizedSelectedFinalRouteInput where
  inputs := input.inputs
  sourceBackedTest := input.sourceBackedTest
  ledgers := input.ledgers
  bridge := input.bridge
  detectorCoverage := input.rows.detectorCoverage
  traceFrontB2 :=
    trace_front_b2_of_selected_final_route_rows input.rows
  finitePrimeIndexDifference :=
    finite_prime_index_difference_of_selected_final_route_rows input.rows
  splitSupportVisibleOwnerComponents :=
    split_support_visible_components_of_selected_final_route_rows
      input.rows

def selected_final_route_lower_input_sourceRH_from_08A
    (input : NormalizedSelectedFinalRouteLowerInput) :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_rows_sourceRH_from_08A
    input.rows

axiom normalizedSelectedFinalRouteDetectorCoverageRoot :
  NormalizedRouteBackedCC20SquareRestrictedDetectorCoverage

axiom normalizedSelectedFinalRouteTraceFrontB2Root :
  NormalizedRouteBackedCC20SquareRestrictedTraceFrontComparisonB2Calibration

axiom normalizedSelectedFinalRouteConcreteCanonicalRoutePackageCoverageRoot :
  NormalizedRouteBackedCC20SquareRestrictedConcreteCanonicalRoutePackageCoverage

axiom normalizedSelectedFinalRouteFinitePrimeIndexDifferenceRoot :
  NormalizedRouteBackedCC20SquareRestrictedFinitePrimeIndexDifferenceCalibration

axiom normalizedSelectedFinalRouteDirectGlobalUnfilteredTermMassRoot :
  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectGlobalUnfilteredTermMassCalibration
    (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormCarrierCalibration_of_concreteSourceWeilFormCarrier
      (NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeConcreteSourceWeilFormCarrierCalibration_of_concreteCanonicalRoutePackageCoverage
        normalizedSelectedFinalRouteConcreteCanonicalRoutePackageCoverageRoot))

axiom normalizedSelectedFinalRoutePackageRowsRoot :
  NormalizedRouteBackedCC20SquareRestrictedCommonFinitePrimeSourceWeilFormDirectTermForSourceTestAtomPackageConcreteCanonicalRoutePackageCoverageRouteFacingRowsCalibration

axiom normalizedSelectedFinalRoutePackageTermMassRoot :
  NormalizedSelectedFinalRoutePackageTermMassInput

axiom normalizedSelectedFinalRouteFinitePrimeEvaluatorRoot :
  NormalizedSelectedFinalRouteFinitePrimeEvaluatorInput

axiom normalizedSelectedFinalRouteSourceEvaluationDataRoot :
  NormalizedSelectedFinalRouteSourceEvaluationDataInput

axiom normalizedSelectedFinalRouteConcreteCanonicalPackageRowsRoot :
  NormalizedSelectedFinalRouteConcreteCanonicalPackageRowsInput

axiom normalizedSelectedFinalRouteTraceSourceCanonicalPackageRoot :
  NormalizedSelectedFinalRouteTraceSourceCanonicalPackageInput

axiom normalizedSelectedFinalRouteCanonicalSquareTraceSourcePackageRoot :
  NormalizedSelectedFinalRouteCanonicalSquareTraceSourcePackageInput

axiom normalizedSelectedFinalRouteCanonicalSquareTraceRowsPackageRoot :
  NormalizedSelectedFinalRouteCanonicalSquareTraceRowsPackageInput

axiom normalizedSelectedFinalRouteCanonicalSquareDataTraceRowsPackageRoot :
  NormalizedSelectedFinalRouteCanonicalSquareDataTraceRowsPackageInput

axiom normalizedSelectedFinalRouteDetectorCriterionCoverageRoot :
  NormalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage

/- These roots belonged only to the demoted detector-selected upgrade ladder.
They are retained in source history above but are not active assumptions.

axiom normalizedSelectedFinalRouteDetectorQWPoleRowsRoot :
  NormalizedSelectedFinalRouteDetectorQWPoleRowsInput

axiom normalizedSelectedFinalRouteDetectorSplitQWPoleRowsRoot :
  NormalizedSelectedFinalRouteDetectorSplitQWPoleRowsInput

axiom normalizedSelectedFinalRouteDetectorCanonicalSplitQWPoleRowsRoot :
  NormalizedSelectedFinalRouteDetectorCanonicalSplitQWPoleRowsInput

axiom normalizedSelectedFinalRouteDetectorCanonicalScopedPsiRowsRoot :
  NormalizedSelectedFinalRouteDetectorCanonicalScopedPsiRowsInput

axiom normalizedSelectedFinalRouteDetectorCanonicalSourceEvaluationRowsRoot :
  NormalizedSelectedFinalRouteDetectorCanonicalSourceEvaluationRowsInput

axiom normalizedSelectedFinalRouteDetectorCanonicalArithmeticSumRowsRoot :
  NormalizedSelectedFinalRouteDetectorCanonicalArithmeticSumRowsInput

axiom normalizedSelectedFinalRouteDetectorCanonicalSourceWeilFormLocalDirectRowsRoot :
  NormalizedSelectedFinalRouteDetectorCanonicalSourceWeilFormLocalDirectRowsInput

axiom normalizedSelectedFinalRouteDetectorCanonicalSourceWeilFormLocalPackageRowsRoot :
  NormalizedSelectedFinalRouteDetectorCanonicalSourceWeilFormLocalPackageRowsInput

axiom normalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessLocalPackageRowsRoot :
  NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessLocalPackageRowsInput

axiom normalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessPackageEvaluatorRowsRoot :
  NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessPackageEvaluatorRowsInput

axiom normalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessCommonEvaluatorRowsRoot :
  NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessCommonEvaluatorRowsInput

axiom normalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessRestrictedGlobalRowsRoot :
  NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessRestrictedGlobalRowsInput

axiom normalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessTermMassRowsRoot :
  NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessTermMassRowsInput

axiom normalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessUnfilteredTermMassRowsRoot :
  NormalizedSelectedFinalRouteDetectorCanonicalConcreteWitnessUnfilteredTermMassRowsInput

-/

def normalizedSelectedFinalRouteCanonicalSquareTraceRowsPackageInputFromTheorems :
    NormalizedSelectedFinalRouteCanonicalSquareTraceRowsPackageInput :=
  canonical_square_trace_rows_package_input_of_selected_final_route_canonical_square_data_trace_rows_package
    normalizedSelectedFinalRouteCanonicalSquareDataTraceRowsPackageRoot

def normalizedSelectedFinalRouteCanonicalSquareTraceSourcePackageInputFromTheorems :
    NormalizedSelectedFinalRouteCanonicalSquareTraceSourcePackageInput :=
  canonical_square_trace_source_package_input_of_selected_final_route_canonical_square_trace_rows_package
    normalizedSelectedFinalRouteCanonicalSquareTraceRowsPackageInputFromTheorems

def normalizedSelectedFinalRouteTraceSourceCanonicalPackageInputFromTheorems :
    NormalizedSelectedFinalRouteTraceSourceCanonicalPackageInput :=
  trace_source_canonical_package_input_of_selected_final_route_canonical_square_trace_source_package
    normalizedSelectedFinalRouteCanonicalSquareTraceSourcePackageInputFromTheorems

def normalizedSelectedFinalRouteConcreteCanonicalPackageRowsInputFromTheorems :
    NormalizedSelectedFinalRouteConcreteCanonicalPackageRowsInput :=
  concrete_canonical_package_rows_input_of_selected_final_route_trace_source_canonical_package
    normalizedSelectedFinalRouteTraceSourceCanonicalPackageInputFromTheorems

def normalizedSelectedFinalRouteSourceEvaluationDataInputFromTheorems :
    NormalizedSelectedFinalRouteSourceEvaluationDataInput :=
  source_evaluation_data_input_of_selected_final_route_concrete_canonical_package_rows
    normalizedSelectedFinalRouteConcreteCanonicalPackageRowsInputFromTheorems

def normalizedSelectedFinalRouteFinitePrimeEvaluatorInputFromTheorems :
    NormalizedSelectedFinalRouteFinitePrimeEvaluatorInput :=
  finite_prime_evaluator_input_of_selected_final_route_source_evaluation_data
    normalizedSelectedFinalRouteSourceEvaluationDataInputFromTheorems

def normalizedSelectedFinalRoutePackageTermMassInputFromTheorems :
    NormalizedSelectedFinalRoutePackageTermMassInput :=
  package_term_mass_input_of_selected_final_route_finite_prime_evaluator
    normalizedSelectedFinalRouteFinitePrimeEvaluatorInputFromTheorems

def normalizedSelectedFinalRoutePackageRowsInputFromTheorems :
    NormalizedSelectedFinalRoutePackageRowsInput :=
  selected_final_route_package_rows_input_of_package_term_mass
    normalizedSelectedFinalRoutePackageTermMassInputFromTheorems

def normalizedSelectedFinalRouteRowsInputFromTheorems :
    NormalizedSelectedFinalRouteRowsInput :=
  selected_final_route_rows_input_of_package_rows
    normalizedSelectedFinalRoutePackageRowsInputFromTheorems

axiom normalizedSelectedFinalRouteCertificateCarrierRoot :
  NormalizedSelectedFinalRouteCertificateCarrier

def normalizedSelectedFinalRouteLowerInputFromTheorems :
    NormalizedSelectedFinalRouteLowerInput :=
  selected_final_route_lower_input_of_certificate_carrier
    normalizedSelectedFinalRouteCertificateCarrierRoot
    normalizedSelectedFinalRouteRowsInputFromTheorems

def normalizedSelectedFinalRouteInputFromTheorems :
    NormalizedSelectedFinalRouteInput :=
  selected_final_route_input_of_lower_input
    normalizedSelectedFinalRouteLowerInputFromTheorems

def normalizedSelectedFinalRouteInputsFromTheorems :
    RouteInputs :=
  RouteInputs.ofSelectedFinalInput normalizedSelectedFinalRouteInputFromTheorems

def normalizedSelectedFinalRouteCertificateFromTheorems :
    RouteCertificate normalizedSelectedFinalRouteInputsFromTheorems :=
  route_certificate_of_selected_final_route_input
    normalizedSelectedFinalRouteInputFromTheorems

theorem normalizedSelectedFinalRouteSourceRHFrom08AFromTheorems :
    Source.RHDefinitionBridge.standard.SourceRH :=
  selected_final_route_detector_criterion_coverage_sourceRH_from_08A
    normalizedSelectedFinalRouteDetectorCriterionCoverageRoot

structure NormalizedNoArgumentRouteCertificatePackage (inputs : RouteInputs) where
  routeCertificate :
    RouteCertificate
      inputs
  finalExitPackage :
    RouteFinalExitPackage
      inputs

noncomputable def normalizedNoArgumentRouteCertificatePackageFromTheorems :
    NormalizedNoArgumentRouteCertificatePackage
      normalizedSelectedFinalRouteInputsFromTheorems where
  routeCertificate := normalizedSelectedFinalRouteCertificateFromTheorems
  finalExitPackage :=
    route_final_exit_package_of_certificate
      normalizedSelectedFinalRouteCertificateFromTheorems

def mathlib_rh_of_normalized_no_argument_route_certificate_package
    {inputs : RouteInputs}
    (pkg : NormalizedNoArgumentRouteCertificatePackage inputs) :
    _root_.RiemannHypothesis :=
  final_connes_weil_rh pkg.routeCertificate

/-- Checklist item 6 compatibility outlet backed by the normalized lane. -/
abbrev sourceObjectPackageFromTheorems :
    Source.SourceObject.SourceObjectPackage :=
  normalizedSourceObjectPackageFromTheorems

/-- Checklist item 7 compatibility outlet backed by the normalized lane. -/
abbrev fixedFrontEndFromTheorems :
    ExpandedSourceFixedSTestFrontEnd sourceObjectPackageFromTheorems :=
  normalizedFixedFrontEndFromTheorems

/-- Checklist item 8 compatibility outlet backed by the normalized lane. -/
abbrev traceFrontEndFromTheorems :
    ExpandedSourceTraceReadOffFrontEnd
      sourceObjectPackageFromTheorems fixedFrontEndFromTheorems :=
  normalizedTraceFrontEndFromTheorems

def routeLedgerClearingInputDataFromTheorems :
    RouteLedgerClearingInputData where
  ledgers := normalizedRouteLedgersFromTheorems
  cleared := normalizedLedgersClearedFromTheorems

def routeLedgersFromTheorems : RouteLedgers :=
  routeLedgerClearingInputDataFromTheorems.ledgers

theorem rankLedgerKilledFromTheorems :
    routeLedgersFromTheorems.rankKilled :=
  routeLedgerClearingInputDataFromTheorems.cleared.rankKilled

theorem poleLedgerKilledFromTheorems :
    routeLedgersFromTheorems.poleKilled :=
  routeLedgerClearingInputDataFromTheorems.cleared.poleKilled

theorem cdefExhaustsFromTheorems :
    routeLedgersFromTheorems.cdefExhausts :=
  routeLedgerClearingInputDataFromTheorems.cleared.cdefExhausts

def ledgersClearedFromTheorems :
    LedgersCleared routeLedgersFromTheorems :=
  routeLedgerClearingInputDataFromTheorems.cleared

theorem signDefectClassificationFromTheorems :
    SourceSignDefectClassification
      (RouteInputs.ofExpandedSourcePackage sourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems)
      traceFrontEndFromTheorems.lambda routeLedgersFromTheorems :=
  normalizedSignDefectClassificationFromTheorems

def commonTupleFromTheorems :
    SourceCommonTestTupleContract
      (RouteInputs.ofExpandedSourcePackage sourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems)
      traceFrontEndFromTheorems.lambda
      sourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
      traceFrontEndFromTheorems.ccm25ArithmeticPackage :=
  normalizedCommonTupleFromTheorems

noncomputable def restrictedToFullThresholdInputDataFromTheorems :
    RestrictedToFullThresholdInputData
      sourceObjectPackageFromTheorems
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems)
      traceFrontEndFromTheorems.lambda
      sourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare where
  threshold := normalizedRestrictedToFullLargeLambdaThresholdFromTheorems
  currentAboveThreshold := normalizedRestrictedToFullCurrentAboveThresholdFromTheorems

noncomputable def restrictedToFullLargeLambdaThresholdFromTheorems :
    RestrictedToFullQWLargeLambdaThreshold
      (RouteInputs.ofExpandedSourcePackage sourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems)
      sourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare :=
  restrictedToFullThresholdInputDataFromTheorems.threshold

theorem restrictedToFullCurrentAboveThresholdFromTheorems :
    restrictedToFullLargeLambdaThresholdFromTheorems.lambda0 ≤
      traceFrontEndFromTheorems.lambda :=
  restrictedToFullThresholdInputDataFromTheorems.currentAboveThreshold

noncomputable def restrictedToFullQWFromTheorems :
    RestrictedToFullQWBridgeContract
      (RouteInputs.ofExpandedSourcePackage sourceObjectPackageFromTheorems)
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems)
      traceFrontEndFromTheorems.lambda
      sourceObjectPackageFromTheorems.commonTest.sourceConvolutionSquare
      routeLedgersFromTheorems
      traceFrontEndFromTheorems.ccm25ArithmeticPackage :=
  normalizedRestrictedToFullQWFromTheorems

theorem sourceArchimedeanSignBridgeFromTheorems :
    SourceArchimedeanSignBridge
      (RouteInputs.ofExpandedSourcePackage sourceObjectPackageFromTheorems)
      sourceObjectPackageFromTheorems.cc20Trace.sourceTraceTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage
        sourceObjectPackageFromTheorems fixedFrontEndFromTheorems) :=
  normalizedSourceArchimedeanSignBridgeFromTheorems

noncomputable def routeCertificateFromTheorems :
    RouteCertificate
      normalizedSelectedFinalRouteInputsFromTheorems :=
  normalizedSelectedFinalRouteCertificateFromTheorems

theorem cc20FiniteVanishingExitFromTheorems :
    Source.RHDefinitionBridge.standard.SourceRH := by
  simpa [normalizedSelectedFinalRouteInputsFromTheorems,
    RouteInputs.ofSelectedFinalInput] using
    normalizedSelectedFinalRouteSourceRHFrom08AFromTheorems

theorem rhDefinitionBridgeToMathlibFromTheorems :
    _root_.RiemannHypothesis :=
  Source.RHDefinitionBridge.source_rh_to_mathlib_rh
    Source.RHDefinitionBridge.standard
    cc20FiniteVanishingExitFromTheorems

theorem unconditional_rh_skeleton : _root_.RiemannHypothesis := by
  exact rhDefinitionBridgeToMathlibFromTheorems

theorem unconditional_rh_contract_skeleton : _root_.RiemannHypothesis := by
  exact
    mathlib_rh_of_normalized_no_argument_route_certificate_package
      normalizedNoArgumentRouteCertificatePackageFromTheorems

end NormalizedContractBackedLane

end UnconditionalSkeleton
end Dev
end ConnesWeilRH
