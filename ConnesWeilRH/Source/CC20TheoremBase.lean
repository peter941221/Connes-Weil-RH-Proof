/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20
import ConnesWeilRH.Source.CC20TraceModel

/-!
# CC20 Lean theorem base

This module gives Goal 1 a Lean-checkable CC20 trace theorem-base layer.  The
compact `CC20Interface` also carries the finite-vanishing RH exit object; this
module keeps that object as explicit data and does not claim Goal 1 discharges
the final CC20 exit.
-/

namespace ConnesWeilRH
namespace Source

/-- Data-bearing Lean theorem base for the CC20 trace source-interface row. -/
structure CC20TheoremBase where
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
  rhDefinitionBridge : RHDefinitionBridge
  cc20RHExitObjectPackage :
    CC20RHExitObjectPackage rhDefinitionBridge

namespace CC20TheoremBase

def dischargedTraceBase
    (M : CC20TraceModel)
    {B : RHDefinitionBridge}
    (rhExit : CC20RHExitObjectPackage B) : CC20TheoremBase where
  archimedeanSymbols := M.archimedeanSymbols
  archimedeanTraceSquare := cc20_source_archimedean_trace_square M
  traceClassTemplate := cc20_source_trace_class_template M
  mellinHalfDensityConvention :=
    cc20_source_mellin_half_density_convention M
  signsAndNormalizations := cc20_source_signs_and_normalizations M
  rhDefinitionBridge := B
  cc20RHExitObjectPackage := rhExit

def toInterface (h : CC20TheoremBase) : CC20Interface where
  archimedeanSymbols := h.archimedeanSymbols
  archimedeanTraceSquare := h.archimedeanTraceSquare
  traceClassTemplate := h.traceClassTemplate
  mellinHalfDensityConvention := h.mellinHalfDensityConvention
  rhDefinitionBridge := h.rhDefinitionBridge
  cc20RHExitObjectPackage := h.cc20RHExitObjectPackage
  signsAndNormalizations := h.signsAndNormalizations

end CC20TheoremBase

end Source
end ConnesWeilRH
