/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Basic

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

end Source
end ConnesWeilRH
