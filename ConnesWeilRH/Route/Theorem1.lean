/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Route.Ledger
import ConnesWeilRH.Source.CCM25Concrete.Package

/-!
# Theorem 1 route interface

This module records the local output expected from the fixed-`S`
source-normalized positive trace theorem.
-/

namespace ConnesWeilRH
namespace Route

structure CC20TraceLegality
    (inputs : RouteInputs)
    (a : inputs.cc20.archimedeanSymbols.Test) where
  traceClass : inputs.cc20.archimedeanSymbols.traceClass a
  cyclicLegal : inputs.cc20.archimedeanSymbols.cyclicLegal a

def CC20NoDefectSourceReadOff
    (inputs : RouteInputs)
    (a : inputs.cc20.archimedeanSymbols.Test) : Prop :=
  inputs.cc20.archimedeanSymbols.supportSquareTrace a =
    inputs.cc20.archimedeanSymbols.sourceNoDefectTrace a

def CC20PositiveTraceNonnegative
    (inputs : RouteInputs)
    (a : inputs.cc20.archimedeanSymbols.Test) : Prop :=
  0 ≤ inputs.cc20.archimedeanSymbols.positiveTrace a

structure CC20TraceSquareReadOff
    (inputs : RouteInputs)
    (a : inputs.cc20.archimedeanSymbols.Test) where
  noDefectSourceReadOff : CC20NoDefectSourceReadOff inputs a
  positiveTraceNonnegative : CC20PositiveTraceNonnegative inputs a

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

structure FullTraceReadOffSource
    (inputs : RouteInputs) (a : inputs.cc20.archimedeanSymbols.Test)
    (g : SourceBackedFixedSTest inputs) where
  noDefectSourceReadOff : CC20NoDefectSourceReadOff inputs a
  ccm25FullQWReadOff : CCM25FullQWReadOff inputs g
  fullTraceReadOffEquality : FullTraceReadOffEquality inputs a g

structure RestrictedTraceReadOffSource
    (inputs : RouteInputs) (a : inputs.cc20.archimedeanSymbols.Test)
    (g : SourceBackedFixedSTest inputs) (lambda : ℝ) where
  ccm25RestrictedQWReadOff : CCM25RestrictedQWReadOff inputs g lambda
  restrictedTraceReadOffEquality :
    RestrictedTraceReadOffEquality inputs a g lambda

structure TraceWeilCompatibilityData
    (inputs : RouteInputs) (a : inputs.cc20.archimedeanSymbols.Test)
    (g : SourceBackedFixedSTest inputs) (lambda : ℝ) where
  fullTraceReadOffEquality : FullTraceReadOffEquality inputs a g
  restrictedTraceReadOffEquality :
    RestrictedTraceReadOffEquality inputs a g lambda
  fullTraceSource : FullTraceReadOffSource inputs a g
  restrictedTraceSource : RestrictedTraceReadOffSource inputs a g lambda

abbrev TraceWeilCompatibility
    (inputs : RouteInputs) (a : inputs.cc20.archimedeanSymbols.Test)
    (g : SourceBackedFixedSTest inputs) (lambda : ℝ) :=
  TraceWeilCompatibilityData inputs a g lambda

def full_trace_read_off_source_of_parts
    {inputs : RouteInputs}
    {a : inputs.cc20.archimedeanSymbols.Test}
    {g : SourceBackedFixedSTest inputs}
    (hnoDefect : CC20NoDefectSourceReadOff inputs a)
    (hfull : CCM25FullQWReadOff inputs g)
    (heq : FullTraceReadOffEquality inputs a g) :
    FullTraceReadOffSource inputs a g :=
  { noDefectSourceReadOff := hnoDefect
    ccm25FullQWReadOff := hfull
    fullTraceReadOffEquality := heq }

def restricted_trace_read_off_source_of_parts
    {inputs : RouteInputs}
    {a : inputs.cc20.archimedeanSymbols.Test}
    {g : SourceBackedFixedSTest inputs} {lambda : ℝ}
    (hrestricted : CCM25RestrictedQWReadOff inputs g lambda)
    (heq : RestrictedTraceReadOffEquality inputs a g lambda) :
    RestrictedTraceReadOffSource inputs a g lambda :=
  { ccm25RestrictedQWReadOff := hrestricted
    restrictedTraceReadOffEquality := heq }

def trace_weil_compatibility_data_of_sources
    {inputs : RouteInputs}
    {a : inputs.cc20.archimedeanSymbols.Test}
    {g : SourceBackedFixedSTest inputs} {lambda : ℝ}
    (hfull : FullTraceReadOffSource inputs a g)
    (hrestricted : RestrictedTraceReadOffSource inputs a g lambda) :
    TraceWeilCompatibilityData inputs a g lambda where
  fullTraceReadOffEquality := hfull.fullTraceReadOffEquality
  restrictedTraceReadOffEquality := hrestricted.restrictedTraceReadOffEquality
  fullTraceSource := hfull
  restrictedTraceSource := hrestricted

def trace_weil_compatibility_of_sources
    {inputs : RouteInputs}
    {a : inputs.cc20.archimedeanSymbols.Test}
    {g : SourceBackedFixedSTest inputs} {lambda : ℝ}
    (hfull : FullTraceReadOffSource inputs a g)
    (hrestricted : RestrictedTraceReadOffSource inputs a g lambda) :
    TraceWeilCompatibility inputs a g lambda :=
  trace_weil_compatibility_data_of_sources
    hfull hrestricted

structure FixedSPositiveTraceReadOff
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs) where
  archimedeanTest : inputs.cc20.archimedeanSymbols.Test
  lambda : ℝ
  traceLegality : CC20TraceLegality inputs archimedeanTest
  testAndQuotientCompatibility : TestAndQuotientCompatibility inputs g
  fixedSSupportSquareTransport :
    FixedSQuantizedSupportSquareTransport inputs archimedeanTest g lambda
  noDefectSourceReadOff : CC20NoDefectSourceReadOff inputs archimedeanTest
  ccm25WeilFormReadOff : CCM25WeilFormReadOff inputs g lambda
  positiveTraceNonnegative :
    CC20PositiveTraceNonnegative inputs archimedeanTest

structure SourceTraceReadOffData
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs) where
  archimedeanTest : inputs.cc20.archimedeanSymbols.Test
  hilbertSchmidtGate :
    inputs.cc20.archimedeanSymbols.hilbertSchmidtGate archimedeanTest
  lambda : ℝ
  oneLtLambda : 1 < lambda
  ccm25ArithmeticPackage :
    Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
      inputs.ccm25.weilSymbols g.weilTest lambda
  testAndQuotientCompatibility : TestAndQuotientCompatibility inputs g
  fixedSSupportSquareTransport :
    FixedSQuantizedSupportSquareTransport inputs archimedeanTest g lambda
  fullTraceReadOffBridge :
    CC20NoDefectSourceReadOff inputs archimedeanTest →
      CCM25FullQWReadOff inputs g →
      FullTraceReadOffSource inputs archimedeanTest g
  restrictedTraceReadOffBridge :
    CCM25RestrictedQWReadOff inputs g lambda →
      RestrictedTraceReadOffSource inputs archimedeanTest g lambda
  positiveTraceNonnegative :
    CC20PositiveTraceNonnegative inputs archimedeanTest

structure ExpandedSourceTraceReadOffFrontEnd
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg) where
  lambda : ℝ
  oneLtLambda : 1 < lambda
  ccm25ArithmeticPackage :
    Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
      (RouteInputs.ofExpandedSourcePackage pkg).ccm25.weilSymbols
      pkg.commonTest.sourceTest lambda
  testAndQuotientCompatibility :
    TestAndQuotientCompatibility
      (RouteInputs.ofExpandedSourcePackage pkg)
      (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
  fixedSSupportSquareTransport :
    FixedSQuantizedSupportSquareTransport
      (RouteInputs.ofExpandedSourcePackage pkg)
      pkg.cc20Trace.sourceTraceTest
      (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
      lambda
  fullTraceReadOffBridge :
    CC20NoDefectSourceReadOff
        (RouteInputs.ofExpandedSourcePackage pkg)
        pkg.cc20Trace.sourceTraceTest →
      CCM25FullQWReadOff
        (RouteInputs.ofExpandedSourcePackage pkg)
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront) →
      FullTraceReadOffSource
        (RouteInputs.ofExpandedSourcePackage pkg)
        pkg.cc20Trace.sourceTraceTest
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
  restrictedTraceReadOffBridge :
    CCM25RestrictedQWReadOff
        (RouteInputs.ofExpandedSourcePackage pkg)
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
        lambda →
      RestrictedTraceReadOffSource
        (RouteInputs.ofExpandedSourcePackage pkg)
        pkg.cc20Trace.sourceTraceTest
        (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront)
        lambda

namespace SourceTraceReadOffData

def ofExpandedSourcePackage
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceFront : ExpandedSourceTraceReadOffFrontEnd pkg fixedFront) :
    SourceTraceReadOffData
      (RouteInputs.ofExpandedSourcePackage pkg)
      (SourceBackedFixedSTest.ofExpandedSourcePackage pkg fixedFront) where
  archimedeanTest := pkg.cc20Trace.sourceTraceTest
  hilbertSchmidtGate :=
    pkg.cc20Trace.sourceHilbertSchmidtGate pkg.cc20Trace.sourceTraceTest
  lambda := traceFront.lambda
  oneLtLambda := traceFront.oneLtLambda
  ccm25ArithmeticPackage := traceFront.ccm25ArithmeticPackage
  testAndQuotientCompatibility := traceFront.testAndQuotientCompatibility
  fixedSSupportSquareTransport := traceFront.fixedSSupportSquareTransport
  fullTraceReadOffBridge := traceFront.fullTraceReadOffBridge
  restrictedTraceReadOffBridge := traceFront.restrictedTraceReadOffBridge
  positiveTraceNonnegative := by
    let inputs := RouteInputs.ofExpandedSourcePackage pkg
    let hgate :=
      pkg.cc20Trace.sourceHilbertSchmidtGate pkg.cc20Trace.sourceTraceTest
    let hlegal := inputs.cc20.traceClassTemplate
      pkg.cc20Trace.sourceTraceTest hgate
    exact pkg.cc20Trace.sourcePositiveTraceNonnegative
      pkg.cc20Trace.sourceTraceTest hlegal.1 hlegal.2

theorem archimedean_test_of_expanded_source_package
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceFront : ExpandedSourceTraceReadOffFrontEnd pkg fixedFront) :
    (ofExpandedSourcePackage pkg fixedFront traceFront).archimedeanTest =
      pkg.cc20Trace.sourceTraceTest :=
  rfl

theorem lambda_of_expanded_source_package
    (pkg : Source.SourceObject.SourceObjectPackage)
    (fixedFront : ExpandedSourceFixedSTestFrontEnd pkg)
    (traceFront : ExpandedSourceTraceReadOffFrontEnd pkg fixedFront) :
    (ofExpandedSourcePackage pkg fixedFront traceFront).lambda =
      traceFront.lambda :=
  rfl

end SourceTraceReadOffData

theorem cc20_trace_legality_of_source_trace_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    (h : SourceTraceReadOffData inputs g) :
    CC20TraceLegality inputs h.archimedeanTest :=
  let hlegal :=
    inputs.cc20.traceClassTemplate h.archimedeanTest h.hilbertSchmidtGate
  { traceClass := hlegal.1
    cyclicLegal := hlegal.2 }

theorem cc20_trace_square_of_source_trace_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    (h : SourceTraceReadOffData inputs g) :
    CC20TraceSquareReadOff inputs h.archimedeanTest :=
  let hlegal := cc20_trace_legality_of_source_trace_data h
  let htrace :=
    inputs.cc20.archimedeanTraceSquare h.archimedeanTest
      hlegal.traceClass hlegal.cyclicLegal
  { noDefectSourceReadOff := htrace.1
    positiveTraceNonnegative := htrace.2 }

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

theorem ccm25_qw_definition_read_off_of_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) :
    CCM25QWDefinitionReadOff inputs g :=
  Source.CCM25Concrete.Package.qw_definition_of_package_components pkg

theorem ccm25_psi_sign_read_off_of_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) :
    CCM25PsiSignReadOff inputs g :=
  Source.CCM25Concrete.Package.psi_sign_of_package_components pkg

theorem ccm25_full_qw_read_off_of_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) :
    CCM25FullQWReadOff inputs g :=
  ⟨ccm25_qw_definition_read_off_of_package pkg,
    ccm25_psi_sign_read_off_of_package pkg⟩

theorem ccm25_qw_lambda_formula_read_off_of_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) :
    CCM25QWLambdaFormulaReadOff inputs g lambda :=
  Source.CCM25Concrete.Package.qw_lambda_formula_of_package_components pkg

theorem ccm25_pole_normalization_read_off_of_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) :
    CCM25PoleNormalizationReadOff inputs g :=
  Source.CCM25Concrete.Package.pole_normalization_of_package_interface
    pkg g.weilTest

theorem ccm25_restricted_qw_read_off_of_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda)
    (hwindow : WindowLambdaCompatibility inputs g lambda) :
    CCM25RestrictedQWReadOff inputs g lambda :=
  ⟨hwindow,
    ccm25_qw_lambda_formula_read_off_of_package pkg,
    ccm25_pole_normalization_read_off_of_package pkg⟩

theorem ccm25_weil_form_read_off_of_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda)
    (hwindow : WindowLambdaCompatibility inputs g lambda) :
    CCM25WeilFormReadOff inputs g lambda :=
  ⟨ccm25_full_qw_read_off_of_package pkg,
    ccm25_restricted_qw_read_off_of_package pkg hwindow⟩

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
  ccm25_weil_form_read_off_of_package h.ccm25ArithmeticPackage
    ⟨h.oneLtLambda, window_support_containment_of_source_backed g h.oneLtLambda,
      lambda_compatible_of_source_backed g h.oneLtLambda⟩

theorem ccm25_full_qw_read_off_of_source_trace_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    (h : SourceTraceReadOffData inputs g) :
    CCM25FullQWReadOff inputs g :=
  ccm25_full_qw_read_off_of_package h.ccm25ArithmeticPackage

theorem ccm25_restricted_qw_read_off_of_source_trace_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    (h : SourceTraceReadOffData inputs g) :
    CCM25RestrictedQWReadOff inputs g h.lambda :=
  ccm25_restricted_qw_read_off_of_package h.ccm25ArithmeticPackage
    ⟨h.oneLtLambda, window_support_containment_of_source_backed g h.oneLtLambda,
      lambda_compatible_of_source_backed g h.oneLtLambda⟩

theorem full_trace_read_off_source_of_bridge
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    (h : SourceTraceReadOffData inputs g)
    (hnoDefect : CC20NoDefectSourceReadOff inputs h.archimedeanTest)
    (hfull : CCM25FullQWReadOff inputs g) :
    FullTraceReadOffSource inputs h.archimedeanTest g :=
  h.fullTraceReadOffBridge hnoDefect hfull

theorem restricted_trace_read_off_source_of_bridge
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    (h : SourceTraceReadOffData inputs g)
    (hrestricted : CCM25RestrictedQWReadOff inputs g h.lambda) :
    RestrictedTraceReadOffSource inputs h.archimedeanTest g h.lambda :=
  h.restrictedTraceReadOffBridge hrestricted

theorem full_trace_read_off_of_source_trace_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    (h : SourceTraceReadOffData inputs g) :
    FullTraceReadOffSource inputs h.archimedeanTest g :=
  let htrace := cc20_trace_square_of_source_trace_data h
  let hfull := ccm25_full_qw_read_off_of_source_trace_data h
  full_trace_read_off_source_of_bridge h
    htrace.noDefectSourceReadOff hfull

theorem restricted_trace_read_off_of_source_trace_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    (h : SourceTraceReadOffData inputs g) :
    RestrictedTraceReadOffSource inputs h.archimedeanTest g h.lambda :=
  restricted_trace_read_off_source_of_bridge h
    (ccm25_restricted_qw_read_off_of_source_trace_data h)

theorem trace_weil_compatibility_of_source_trace_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    (h : SourceTraceReadOffData inputs g) :
    TraceWeilCompatibility inputs h.archimedeanTest g h.lambda :=
  trace_weil_compatibility_of_sources
    (full_trace_read_off_of_source_trace_data h)
    (restricted_trace_read_off_of_source_trace_data h)

def fixed_s_read_off_of_source_trace_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    (h : SourceTraceReadOffData inputs g) :
    FixedSPositiveTraceReadOff inputs g :=
  let hlegal := cc20_trace_legality_of_source_trace_data h
  let htrace := cc20_trace_square_of_source_trace_data h
  let hweil := ccm25_weil_form_read_off_of_source_trace_data h
  { archimedeanTest := h.archimedeanTest
    lambda := h.lambda
    traceLegality := hlegal
    testAndQuotientCompatibility := h.testAndQuotientCompatibility
    fixedSSupportSquareTransport := h.fixedSSupportSquareTransport
    noDefectSourceReadOff := htrace.noDefectSourceReadOff
    ccm25WeilFormReadOff := hweil
    positiveTraceNonnegative := h.positiveTraceNonnegative }

def theorem1_read_off
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    (h : SourceTraceReadOffData inputs g) :
    FixedSPositiveTraceReadOff inputs g :=
  fixed_s_read_off_of_source_trace_data h

end Route
end ConnesWeilRH
