/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM24SourceModel
import ConnesWeilRH.Source.CCM25TheoremBase

/-!
# Shared analytic source-model constructors

This module connects the source-facing analytic core to the three core
source-model inputs.  It is intentionally below the route layer: the only
extra inputs are the still-mathematical row packages needed to build the CCM24
semilocal object and the CCM25 finite-prime arithmetic rows.
-/

namespace ConnesWeilRH
namespace Source
namespace AnalyticCore

/--
One source-backed constructor input for the three core source-model bodies.

The same `SourceAnalyticCore` supplies the test algebra, CCM24 support/window
symbols, CCM25 Weil-form symbols, and CC20 normalized trace-scale seed.  The
remaining fields are the real proof rows not derivable from the current core
definitions alone.
-/
structure SourceModelConstructorInput where
  core : SourceAnalyticCore
  semilocalRows : SourceSemilocalRows core.supportWindow
  finitePrimeArithmeticCertificates :
    CCM25Concrete.FinitePrimeInterface.FixedLambdaArithmeticSourceTestCertificatesForAllTests
      core.toWeilFormSymbols

namespace SourceModelConstructorInput

def toCCM24SemilocalObjectPackage
    (input : SourceModelConstructorInput) :
    SourceObject.CCM24SemilocalObjectPackage :=
  input.core.supportWindow.toCCM24SemilocalObjectPackage input.semilocalRows

noncomputable def toCCM25ArithmeticConstructorInput
    (input : SourceModelConstructorInput) :
    CCM25SourceArithmeticConstructorInput :=
  input.core.weilForm.toCCM25SourceArithmeticConstructorInput
    input.finitePrimeArithmeticCertificates

noncomputable def toCCM25WeilObjectPackage
    (input : SourceModelConstructorInput) :
    SourceObject.CCM25WeilObjectPackage :=
  input.toCCM25ArithmeticConstructorInput.toCCM25WeilObjectPackage

def toNormalizedLegalSquareTraceScaleSymbols
    (input : SourceModelConstructorInput) :
    CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols :=
  input.core.toNormalizedLegalSquareTraceScaleSymbols

noncomputable def toCCM24SourceModel
    (input : SourceModelConstructorInput) :
    CCM24SourceModel :=
  ccm24_source_model_of_semilocal_object
    input.toCCM24SemilocalObjectPackage

noncomputable def toCCM25SourceModel
    (input : SourceModelConstructorInput) :
    CCM25SourceModel :=
  input.toCCM25ArithmeticConstructorInput.toCCM25SourceModel

def toCC20TraceModel
    (input : SourceModelConstructorInput) :
    CC20TraceModel :=
  CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
    input.toNormalizedLegalSquareTraceScaleSymbols

@[simp]
theorem ccm24_symbols
    (input : SourceModelConstructorInput) :
    input.toCCM24SemilocalObjectPackage.semilocalSymbols =
      input.core.toSemilocalModelSymbols :=
  rfl

@[simp]
theorem ccm25_symbols
    (input : SourceModelConstructorInput) :
    input.toCCM25WeilObjectPackage.weilSymbols =
      input.core.toWeilFormSymbols :=
  rfl

@[simp]
theorem ccm25_source_model_symbols
    (input : SourceModelConstructorInput) :
    input.toCCM25SourceModel.toWeilFormSymbols =
      input.core.toWeilFormSymbols := by
  simp [toCCM25SourceModel, toCCM25ArithmeticConstructorInput,
    SourceWeilFormData.toCCM25SourceArithmeticConstructorInput,
    SourceAnalyticCore.toWeilFormSymbols]

theorem cc20_trace_model_eq_seed
    (input : SourceModelConstructorInput) :
    input.toCC20TraceModel =
      CC20Concrete.TraceScale.normalizedLegalSquareTraceScaleToCC20TraceModel
        input.toNormalizedLegalSquareTraceScaleSymbols :=
  rfl

end SourceModelConstructorInput

end AnalyticCore
end Source
end ConnesWeilRH
