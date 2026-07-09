/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Route.CC20RouteRealization

/-!
# 09B package source-data certificate-family rows

This scratch module audits whether the current trace-realization constructor
ties the route package certificate family to the route source-data owner.
-/

namespace ConnesWeilRH
namespace Dev
namespace Parallel09B

open Route Source

private abbrev fixedLambdaSourceTestCertificates
    {W : WeilFormSymbols}
    (data :
      Source.CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
        W) :=
  Source.CCM25Concrete.FinitePrimeSourceData.fixedLambdaArithmeticSourceTestCertificatesForAllTests
    data

theorem traceRealization_finitePrimeSourceDataOwner_eq_input
    {rho : ℂ}
    {detector :
      YoshidaDetector
        normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho}
    {inputs : RouteInputs}
    (baseSourceBackedTest : SourceBackedFixedSTest inputs)
    (finitePrimeSourceDataOwner :
      Source.CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
        inputs.ccm25.weilSymbols)
    (lambda : ℝ) (oneLtLambda : 1 < lambda)
    (rows :
      Source.CCM25Concrete.Interface.ConcreteCCM25ArithmeticRows
        inputs.ccm25.weilSymbols)
    (readOff :
      NormalizedRouteBackedYoshidaDetectorArchimedeanReadOff
        detector inputs) :
    let realization :=
      normalizedRouteBackedYoshidaDetectorArchimedeanTraceRealization_of_readOff
        baseSourceBackedTest finitePrimeSourceDataOwner lambda oneLtLambda rows
        readOff
    realization.finitePrimeSourceDataOwner = finitePrimeSourceDataOwner := by
  rfl

theorem traceRealization_packageCertificateFamily_eq_inputRows
    {rho : ℂ}
    {detector :
      YoshidaDetector
        normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho}
    {inputs : RouteInputs}
    (baseSourceBackedTest : SourceBackedFixedSTest inputs)
    (finitePrimeSourceDataOwner :
      Source.CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
        inputs.ccm25.weilSymbols)
    (lambda : ℝ) (oneLtLambda : 1 < lambda)
    (rows :
      Source.CCM25Concrete.Interface.ConcreteCCM25ArithmeticRows
        inputs.ccm25.weilSymbols)
    (readOff :
      NormalizedRouteBackedYoshidaDetectorArchimedeanReadOff
        detector inputs) :
    let realization :=
      normalizedRouteBackedYoshidaDetectorArchimedeanTraceRealization_of_readOff
        baseSourceBackedTest finitePrimeSourceDataOwner lambda oneLtLambda rows
        readOff
    realization.ccm25ArithmeticPackage.rows.finitePrimeArithmeticCertificates =
      rows.finitePrimeArithmeticCertificates := by
  rfl

theorem traceRealization_packageCertificateFamily_eq_sourceData_of_inputRows_eq
    {rho : ℂ}
    {detector :
      YoshidaDetector
        normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho}
    {inputs : RouteInputs}
    (baseSourceBackedTest : SourceBackedFixedSTest inputs)
    (finitePrimeSourceDataOwner :
      Source.CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
        inputs.ccm25.weilSymbols)
    (lambda : ℝ) (oneLtLambda : 1 < lambda)
    (rows :
      Source.CCM25Concrete.Interface.ConcreteCCM25ArithmeticRows
        inputs.ccm25.weilSymbols)
    (readOff :
      NormalizedRouteBackedYoshidaDetectorArchimedeanReadOff
        detector inputs)
    (hrows :
      rows.finitePrimeArithmeticCertificates =
        fixedLambdaSourceTestCertificates finitePrimeSourceDataOwner) :
    let realization :=
      normalizedRouteBackedYoshidaDetectorArchimedeanTraceRealization_of_readOff
        baseSourceBackedTest finitePrimeSourceDataOwner lambda oneLtLambda rows
        readOff
    realization.ccm25ArithmeticPackage.rows.finitePrimeArithmeticCertificates =
      fixedLambdaSourceTestCertificates realization.finitePrimeSourceDataOwner := by
  simpa using hrows

theorem traceRealization_packageCertificateFamily_target_iff_inputRows_eq
    {rho : ℂ}
    {detector :
      YoshidaDetector
        normalizedCC20TestSpace cc20TripleFiniteVanishingSet rho}
    {inputs : RouteInputs}
    (baseSourceBackedTest : SourceBackedFixedSTest inputs)
    (finitePrimeSourceDataOwner :
      Source.CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
        inputs.ccm25.weilSymbols)
    (lambda : ℝ) (oneLtLambda : 1 < lambda)
    (rows :
      Source.CCM25Concrete.Interface.ConcreteCCM25ArithmeticRows
        inputs.ccm25.weilSymbols)
    (readOff :
      NormalizedRouteBackedYoshidaDetectorArchimedeanReadOff
        detector inputs) :
    let realization :=
      normalizedRouteBackedYoshidaDetectorArchimedeanTraceRealization_of_readOff
        baseSourceBackedTest finitePrimeSourceDataOwner lambda oneLtLambda rows
        readOff
    (realization.ccm25ArithmeticPackage.rows.finitePrimeArithmeticCertificates =
        fixedLambdaSourceTestCertificates realization.finitePrimeSourceDataOwner) ↔
      rows.finitePrimeArithmeticCertificates =
        fixedLambdaSourceTestCertificates finitePrimeSourceDataOwner := by
  rfl

end Parallel09B
end Dev
end ConnesWeilRH
