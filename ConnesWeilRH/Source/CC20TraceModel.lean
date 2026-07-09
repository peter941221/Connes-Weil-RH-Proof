/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.ObjectDerivations

/-!
# CC20 trace source model

This module gives Goal 1B a source-facing model for the CC20 trace theorem
base. The finite-vanishing RH exit object is deliberately absent here; that
exit remains later Goal 5 data.
-/

namespace ConnesWeilRH
namespace Source

/-- Source-facing CC20 trace data before the finite-vanishing RH exit. -/
structure CC20TraceModel where
  archimedeanSymbols : ArchimedeanTraceSymbols
  archimedeanTraceSquare :
    ArchimedeanTraceSymbols.TraceSquareStatement archimedeanSymbols
  traceClassTemplate :
    ArchimedeanTraceSymbols.TraceClassTemplateStatement archimedeanSymbols
  ordinaryTraceSupportSquare :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      archimedeanSymbols
  mellinHalfDensityConvention :
    ArchimedeanTraceSymbols.MellinHalfDensityConventionStatement
      archimedeanSymbols
  signsAndNormalizations :
    ArchimedeanTraceSymbols.SignsAndNormalizationsStatement
      archimedeanSymbols

theorem cc20_source_archimedean_trace_square
    (M : CC20TraceModel) :
    ArchimedeanTraceSymbols.TraceSquareStatement M.archimedeanSymbols :=
  M.archimedeanTraceSquare

theorem cc20_source_trace_class_template
    (M : CC20TraceModel) :
    ArchimedeanTraceSymbols.TraceClassTemplateStatement
      M.archimedeanSymbols :=
  M.traceClassTemplate

theorem cc20_source_ordinary_trace_support_square
    (M : CC20TraceModel) :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      M.archimedeanSymbols :=
  M.ordinaryTraceSupportSquare

theorem cc20_source_mellin_half_density_convention
    (M : CC20TraceModel) :
    ArchimedeanTraceSymbols.MellinHalfDensityConventionStatement
      M.archimedeanSymbols :=
  M.mellinHalfDensityConvention

theorem cc20_source_signs_and_normalizations
    (M : CC20TraceModel) :
    ArchimedeanTraceSymbols.SignsAndNormalizationsStatement
      M.archimedeanSymbols :=
  M.signsAndNormalizations

def cc20_trace_model_of_trace_object
    (pkg : SourceObject.CC20TraceObjectPackage) :
    CC20TraceModel where
  archimedeanSymbols := pkg.archimedeanSymbols
  archimedeanTraceSquare := by
    intro g htrace hcyclic
    exact
      ⟨pkg.sourceSupportSquareTraceReadOff g htrace hcyclic,
        pkg.sourcePositiveTraceNonnegative g htrace hcyclic⟩
  traceClassTemplate := pkg.sourceTraceClassCyclicityTemplate
  ordinaryTraceSupportSquare := pkg.sourceOrdinaryTraceSupportSquare
  mellinHalfDensityConvention := pkg.sourceMellinHalfDensityCompatibility
  signsAndNormalizations := pkg.sourceCC20SignNormalizations

@[simp]
theorem cc20_trace_model_of_trace_object_symbols
    (pkg : SourceObject.CC20TraceObjectPackage) :
    (cc20_trace_model_of_trace_object pkg).archimedeanSymbols =
      pkg.archimedeanSymbols :=
  rfl

theorem cc20_trace_model_of_trace_object_trace_class
    (pkg : SourceObject.CC20TraceObjectPackage) :
    (cc20_trace_model_of_trace_object pkg).traceClassTemplate =
      pkg.sourceTraceClassCyclicityTemplate :=
  rfl

theorem cc20_trace_model_of_trace_object_ordinary_trace
    (pkg : SourceObject.CC20TraceObjectPackage) :
    (cc20_trace_model_of_trace_object pkg).ordinaryTraceSupportSquare =
      pkg.sourceOrdinaryTraceSupportSquare :=
  rfl

theorem cc20_trace_model_of_trace_object_mellin
    (pkg : SourceObject.CC20TraceObjectPackage) :
    (cc20_trace_model_of_trace_object pkg).mellinHalfDensityConvention =
      pkg.sourceMellinHalfDensityCompatibility :=
  rfl

theorem cc20_trace_model_of_trace_object_signs
    (pkg : SourceObject.CC20TraceObjectPackage) :
    (cc20_trace_model_of_trace_object pkg).signsAndNormalizations =
      pkg.sourceCC20SignNormalizations :=
  rfl

end Source
end ConnesWeilRH
