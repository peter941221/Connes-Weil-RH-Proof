/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Route.Ledger

/-!
# Theorem 1 route interface

This module records the local output expected from the fixed-`S`
source-normalized positive trace theorem.
-/

namespace ConnesWeilRH
namespace Route

def CC20TraceLegality
    (inputs : RouteInputs)
    (a : inputs.cc20.archimedeanSymbols.Test) : Prop :=
  inputs.cc20.archimedeanSymbols.traceClass a ∧
    inputs.cc20.archimedeanSymbols.cyclicLegal a

def CC20NoDefectSourceReadOff
    (inputs : RouteInputs)
    (a : inputs.cc20.archimedeanSymbols.Test) : Prop :=
  inputs.cc20.archimedeanSymbols.supportSquareTrace a =
    inputs.cc20.archimedeanSymbols.sourceNoDefectTrace a

def CC20PositiveTraceNonnegative
    (inputs : RouteInputs)
    (a : inputs.cc20.archimedeanSymbols.Test) : Prop :=
  0 ≤ inputs.cc20.archimedeanSymbols.positiveTrace a

def CC20TraceSquareReadOff
    (inputs : RouteInputs)
    (a : inputs.cc20.archimedeanSymbols.Test) : Prop :=
  CC20NoDefectSourceReadOff inputs a ∧
    CC20PositiveTraceNonnegative inputs a

def WindowLambdaCompatibility
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  1 < lambda ∧
    WindowSupportContainment inputs g lambda ∧
      inputs.ccm24.semilocalSymbols.lambdaCompatible g.window lambda

def CCM25QWDefinitionReadOff
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs) : Prop :=
  let W := inputs.ccm25.weilSymbols
  W.qw g.weilTest g.weilTest =
    W.psi (W.convolutionStar g.weilTest g.weilTest)

def CCM25PsiSignReadOff
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs) : Prop :=
  let W := inputs.ccm25.weilSymbols
  W.psi (W.convolutionStar g.weilTest g.weilTest) =
    W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) -
      W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) -
        ∑ n ∈ W.globalPrimeIndexSet,
          W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest)

def CCM25FullQWReadOff
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs) : Prop :=
  CCM25QWDefinitionReadOff inputs g ∧
    CCM25PsiSignReadOff inputs g

def CCM25QWLambdaFormulaReadOff
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  let W := inputs.ccm25.weilSymbols
  W.qwLambda lambda g.weilTest g.weilTest =
    W.archimedeanTerm
        (W.convolutionStar g.weilTest g.weilTest) +
      W.polePairing g.weilTest -
        ∑ n ∈ W.restrictedPrimeIndexSet lambda,
        W.vonMangoldtWeight n *
          W.primePowerPairing n g.weilTest g.weilTest

def CCM25PoleNormalizationReadOff
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs) : Prop :=
  let W := inputs.ccm25.weilSymbols
  W.polePairing g.weilTest =
    W.poleFunctional (W.convolutionStar g.weilTest g.weilTest)

def CCM25RestrictedQWReadOff
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  WindowLambdaCompatibility inputs g lambda ∧
    CCM25QWLambdaFormulaReadOff inputs g lambda ∧
      CCM25PoleNormalizationReadOff inputs g

def CCM25WeilFormReadOff
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  CCM25FullQWReadOff inputs g ∧
    CCM25RestrictedQWReadOff inputs g lambda

def TestHalfDensityCompatibility
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs) : Prop :=
  (Source.cc20MellinHalfDensityConvention
      inputs.cc20.archimedeanSymbols).Holds ∧
    CCM25FullQWReadOff inputs g

def TateDirectionsToPoleLedger
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs) : Prop :=
  CCM25PoleNormalizationReadOff inputs g

def TestAndQuotientCompatibility
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs) : Prop :=
  TestHalfDensityCompatibility inputs g ∧
    TateDirectionsToPoleLedger inputs g

def FixedSProjectionTransport
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  WindowSupportContainment inputs g lambda ∧
    inputs.ccm24.semilocalSymbols.lambdaCompatible g.window lambda

def FixedSPhasePullback
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs) : Prop :=
  inputs.ccm24.semilocalSymbols.boundedComparisonMap g.placeSet ∧
    inputs.ccm24.semilocalSymbols.boundedComparisonInverse g.placeSet ∧
      inputs.cc20.archimedeanSymbols.uInfinityNormalized ∧
        inputs.cc20.archimedeanSymbols.qduNormalized

def FixedSNoDefectSupportSquareTemplate
    (inputs : RouteInputs)
    (a : inputs.cc20.archimedeanSymbols.Test) : Prop :=
  CC20NoDefectSourceReadOff inputs a

def FixedSDefectClassification
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  FixedSProjectionTransport inputs g lambda ∧
    FixedSPhasePullback inputs g

def TraceClassCyclicSupportSquareIdentity
    (inputs : RouteInputs)
    (a : inputs.cc20.archimedeanSymbols.Test) : Prop :=
  CC20TraceLegality inputs a

structure FixedSQuantizedSupportSquareTransport
    (inputs : RouteInputs)
    (a : inputs.cc20.archimedeanSymbols.Test)
    (g : SourceBackedFixedSTest inputs) (lambda : ℝ) where
  projectionTransport : FixedSProjectionTransport inputs g lambda
  phasePullback : FixedSPhasePullback inputs g
  noDefectTemplate : FixedSNoDefectSupportSquareTemplate inputs a
  defectClassification : FixedSDefectClassification inputs g lambda
  traceLegality : TraceClassCyclicSupportSquareIdentity inputs a

def TraceWeilCompatibility
    (inputs : RouteInputs) (a : inputs.cc20.archimedeanSymbols.Test)
    (g : SourceBackedFixedSTest inputs) (lambda : ℝ) : Prop :=
  let W := inputs.ccm25.weilSymbols
  CC20NoDefectSourceReadOff inputs a ∧
    CCM25WeilFormReadOff inputs g lambda ∧
      inputs.cc20.archimedeanSymbols.sourceNoDefectTrace a =
        W.qw g.weilTest g.weilTest ∧
        inputs.cc20.archimedeanSymbols.supportSquareTrace a =
          W.qwLambda lambda g.weilTest g.weilTest

def FullTraceReadOffEquality
    (inputs : RouteInputs) (a : inputs.cc20.archimedeanSymbols.Test)
    (g : SourceBackedFixedSTest inputs) : Prop :=
  inputs.cc20.archimedeanSymbols.sourceNoDefectTrace a =
    inputs.ccm25.weilSymbols.qw g.weilTest g.weilTest

def RestrictedTraceReadOffEquality
    (inputs : RouteInputs) (a : inputs.cc20.archimedeanSymbols.Test)
    (g : SourceBackedFixedSTest inputs) (lambda : ℝ) : Prop :=
  inputs.cc20.archimedeanSymbols.supportSquareTrace a =
    inputs.ccm25.weilSymbols.qwLambda lambda g.weilTest g.weilTest

def FullTraceReadOffSource
    (inputs : RouteInputs) (a : inputs.cc20.archimedeanSymbols.Test)
    (g : SourceBackedFixedSTest inputs) : Prop :=
  CC20NoDefectSourceReadOff inputs a ∧
    CCM25FullQWReadOff inputs g ∧
    FullTraceReadOffEquality inputs a g

def RestrictedTraceReadOffSource
    (inputs : RouteInputs) (a : inputs.cc20.archimedeanSymbols.Test)
    (g : SourceBackedFixedSTest inputs) (lambda : ℝ) : Prop :=
  CCM25RestrictedQWReadOff inputs g lambda ∧
    RestrictedTraceReadOffEquality inputs a g lambda

def FixedSPositiveTraceReadOff
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs) : Prop :=
  ∃ a : inputs.cc20.archimedeanSymbols.Test,
    ∃ lambda : ℝ,
      ∃ weilIdentification : Prop,
        CC20TraceLegality inputs a ∧
          TestAndQuotientCompatibility inputs g ∧
            FixedSQuantizedSupportSquareTransport inputs a g lambda ∧
              CC20NoDefectSourceReadOff inputs a ∧
                CCM25WeilFormReadOff inputs g lambda ∧
                  weilIdentification ∧
                    CC20PositiveTraceNonnegative inputs a

structure SourceTraceReadOffData
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs) where
  archimedeanTest : inputs.cc20.archimedeanSymbols.Test
  hilbertSchmidtGate :
    inputs.cc20.archimedeanSymbols.hilbertSchmidtGate archimedeanTest
  lambda : ℝ
  oneLtLambda : 1 < lambda
  testAndQuotientCompatibility : TestAndQuotientCompatibility inputs g
  fixedSSupportSquareTransport :
    FixedSQuantizedSupportSquareTransport inputs archimedeanTest g lambda
  traceWeilCompatibility :
    Prop
  weilIdentification :
    Prop
  fullTraceReadOffBridge :
    CC20NoDefectSourceReadOff inputs archimedeanTest →
      CCM25FullQWReadOff inputs g →
      FullTraceReadOffSource inputs archimedeanTest g
  restrictedTraceReadOffBridge :
    CCM25RestrictedQWReadOff inputs g lambda →
      RestrictedTraceReadOffSource inputs archimedeanTest g lambda
  traceWeilCompatibilityBridge :
    AdmissibleForTheorem1 g.test →
      CC20NoDefectSourceReadOff inputs archimedeanTest →
        CCM25WeilFormReadOff inputs g lambda →
          FullTraceReadOffEquality inputs archimedeanTest g →
            RestrictedTraceReadOffEquality inputs archimedeanTest g lambda →
              traceWeilCompatibility
  weilIdentificationBridge :
    traceWeilCompatibility →
      CC20PositiveTraceNonnegative inputs archimedeanTest →
        weilIdentification

theorem cc20_trace_legality_of_source_trace_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    (h : SourceTraceReadOffData inputs g) :
    CC20TraceLegality inputs h.archimedeanTest :=
  inputs.cc20.traceClassTemplate h.archimedeanTest h.hilbertSchmidtGate

theorem cc20_trace_square_of_source_trace_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    (h : SourceTraceReadOffData inputs g) :
    CC20TraceSquareReadOff inputs h.archimedeanTest :=
  let hlegal := cc20_trace_legality_of_source_trace_data h
  inputs.cc20.archimedeanTraceSquare h.archimedeanTest hlegal.1 hlegal.2

theorem ccm25_qw_definition_read_off
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs} :
    CCM25QWDefinitionReadOff inputs g :=
  inputs.ccm25.qwDefinition.1 g.weilTest g.weilTest

theorem ccm25_psi_sign_read_off
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs} :
    CCM25PsiSignReadOff inputs g :=
  inputs.ccm25.qwDefinition.2
    (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest)

theorem ccm25_full_qw_read_off
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs} :
    CCM25FullQWReadOff inputs g :=
  ⟨ccm25_qw_definition_read_off, ccm25_psi_sign_read_off⟩

theorem ccm25_qw_lambda_formula_read_off
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} (hlambda : 1 < lambda) :
    CCM25QWLambdaFormulaReadOff inputs g lambda :=
  inputs.ccm25.qwLambdaFormula lambda hlambda g.weilTest

theorem ccm25_pole_normalization_read_off
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs} :
    CCM25PoleNormalizationReadOff inputs g :=
  inputs.ccm25.poleNormalization g.weilTest

theorem ccm25_restricted_qw_read_off
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} (hlambda : 1 < lambda) :
    CCM25RestrictedQWReadOff inputs g lambda :=
  ⟨⟨hlambda, window_support_containment_of_source_backed g hlambda,
      lambda_compatible_of_source_backed g hlambda⟩,
    ccm25_qw_lambda_formula_read_off hlambda,
    ccm25_pole_normalization_read_off⟩

theorem ccm25_weil_form_read_off
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} (hlambda : 1 < lambda) :
    CCM25WeilFormReadOff inputs g lambda :=
  ⟨ccm25_full_qw_read_off,
    ccm25_restricted_qw_read_off hlambda⟩

theorem ccm25_weil_form_read_off_of_source_trace_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    (h : SourceTraceReadOffData inputs g) :
    CCM25WeilFormReadOff inputs g h.lambda :=
  ccm25_weil_form_read_off h.oneLtLambda

theorem ccm25_full_qw_read_off_of_source_trace_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    (_h : SourceTraceReadOffData inputs g) :
    CCM25FullQWReadOff inputs g :=
  ccm25_full_qw_read_off

theorem ccm25_restricted_qw_read_off_of_source_trace_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    (h : SourceTraceReadOffData inputs g) :
    CCM25RestrictedQWReadOff inputs g h.lambda :=
  ccm25_restricted_qw_read_off h.oneLtLambda

theorem full_trace_read_off_of_source_trace_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    (h : SourceTraceReadOffData inputs g) :
    FullTraceReadOffSource inputs h.archimedeanTest g :=
  let htrace := cc20_trace_square_of_source_trace_data h
  let hfull := ccm25_full_qw_read_off_of_source_trace_data h
  h.fullTraceReadOffBridge htrace.1 hfull

theorem restricted_trace_read_off_of_source_trace_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    (h : SourceTraceReadOffData inputs g) :
    RestrictedTraceReadOffSource inputs h.archimedeanTest g h.lambda :=
  h.restrictedTraceReadOffBridge
    (ccm25_restricted_qw_read_off_of_source_trace_data h)

theorem trace_weil_compatibility_of_source_trace_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    (h : SourceTraceReadOffData inputs g) :
    h.traceWeilCompatibility :=
  let htrace := cc20_trace_square_of_source_trace_data h
  let hweil := ccm25_weil_form_read_off_of_source_trace_data h
  let hfull := full_trace_read_off_of_source_trace_data h
  let hrestricted := restricted_trace_read_off_of_source_trace_data h
  h.traceWeilCompatibilityBridge
    (admissible_for_theorem1_of_source_backed g) htrace.1 hweil
    hfull.2.2 hrestricted.2

theorem fixed_s_read_off_of_source_trace_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    (h : SourceTraceReadOffData inputs g) :
    FixedSPositiveTraceReadOff inputs g :=
  let hlegal := cc20_trace_legality_of_source_trace_data h
  let htrace := cc20_trace_square_of_source_trace_data h
  let hweil := ccm25_weil_form_read_off_of_source_trace_data h
  let hcompat := trace_weil_compatibility_of_source_trace_data h
  ⟨h.archimedeanTest, h.lambda, h.weilIdentification,
    hlegal, h.testAndQuotientCompatibility,
    h.fixedSSupportSquareTransport, htrace.1, hweil,
    h.weilIdentificationBridge hcompat htrace.2,
    htrace.2⟩

theorem theorem1_read_off
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    (h : SourceTraceReadOffData inputs g) :
    FixedSPositiveTraceReadOff inputs g :=
  fixed_s_read_off_of_source_trace_data h

end Route
end ConnesWeilRH
