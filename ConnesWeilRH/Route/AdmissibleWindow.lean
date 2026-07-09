/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Route.Definitions

/-!
# Admissible windows

Theorem 1 may only be used when the support window, finite-prime visibility, and
fixed-`S` assumptions have been bundled.
-/

namespace ConnesWeilRH
namespace Route

def AdmissibleForTheorem1 (g : FixedSTest) : Prop :=
  g.admissibleWindow ∧ g.finitePrimesVisible

def WindowSupportContainment
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  inputs.ccm24.supportInWindow g.semilocalTest g.window ∧
    inputs.ccm24.fourierSupportInWindow
        g.semilocalTest g.window ∧
      inputs.ccm24.convolutionSupportTransported
          g.semilocalTest g.window ∧
        inputs.ccm24.windowContainedInLambda
          g.window lambda

theorem admissible_window_of_test
    {g : FixedSTest} (h : AdmissibleForTheorem1 g) :
    g.admissibleWindow :=
  h.1

theorem finite_primes_visible_of_test
    {g : FixedSTest} (h : AdmissibleForTheorem1 g) :
    g.finitePrimesVisible :=
  h.2

theorem finite_prime_visibility_statement_of_source_backed
    {inputs : RouteInputs} (g : SourceBackedFixedSTest inputs) :
    WeilFormSymbols.FinitePrimeVisibilityStatement inputs.ccm25.weilSymbols
      g.weilTest g.weilTest :=
  g.finitePrimeRouteRows.visibilityStatement

theorem global_prime_index_covers_of_source_backed
    {inputs : RouteInputs} (g : SourceBackedFixedSTest inputs) :
  WeilFormSymbols.GlobalPrimeIndexCoverageStatement
      inputs.ccm25.weilSymbols
      (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest) :=
  (finite_prime_visibility_statement_of_source_backed g).globalPrimeIndexCoverage

theorem restricted_prime_index_covers_of_source_backed
    {inputs : RouteInputs} (g : SourceBackedFixedSTest inputs)
    {lambda : ℝ} (hlambda : 1 < lambda) :
  WeilFormSymbols.RestrictedPrimeIndexCoverageStatement
      inputs.ccm25.weilSymbols lambda
      (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest) :=
  (finite_prime_visibility_statement_of_source_backed g).restrictedPrimeIndexCoverage
    lambda hlambda

theorem finite_prime_term_normalization_of_source_backed
    {inputs : RouteInputs} (g : SourceBackedFixedSTest inputs) :
  WeilFormSymbols.FinitePrimeTermNormalizationStatement
      inputs.ccm25.weilSymbols g.weilTest g.weilTest :=
  g.finitePrimeRouteRows.finitePrimeTermNormalization

theorem finite_primes_visible_of_source_backed
    {inputs : RouteInputs} (g : SourceBackedFixedSTest inputs) :
    g.test.finitePrimesVisible :=
  g.finitePrimeRouteRows.finitePrimesVisible

theorem triple_vanishing_statement_of_source_backed
    {inputs : RouteInputs} (g : SourceBackedFixedSTest inputs) :
    TripleVanishingSymbols.TripleVanishingStatement
      g.tripleVanishingSymbols :=
  g.tripleVanishingRouteRows.sourceTripleVanishing

theorem triple_vanishing_of_source_backed
    {inputs : RouteInputs} (g : SourceBackedFixedSTest inputs) :
    g.test.tripleVanishing :=
  g.tripleVanishingRouteRows.routeTripleVanishing

theorem admissible_for_theorem1_of_source_backed
    {inputs : RouteInputs} (g : SourceBackedFixedSTest inputs) :
    AdmissibleForTheorem1 g.test :=
  ⟨g.admissibleWindow, finite_primes_visible_of_source_backed g⟩

theorem canonical_model_compatibility_of_source_backed
    {inputs : RouteInputs} (g : SourceBackedFixedSTest inputs) :
    inputs.ccm24.scalingActionImplemented g.placeSet ∧
      inputs.ccm24.fourierGradingCompatible g.placeSet :=
  g.ccm24RouteConsumerRows.canonicalModelCompatibility

theorem support_transport_of_source_backed
    {inputs : RouteInputs} (g : SourceBackedFixedSTest inputs) :
    inputs.ccm24.supportTransported g.semilocalTest
        g.window ∧
      inputs.ccm24.convolutionSupportTransported
        g.semilocalTest g.window :=
  g.ccm24RouteConsumerRows.supportTransportRows

theorem bounded_comparison_of_source_backed
    {inputs : RouteInputs} (g : SourceBackedFixedSTest inputs) :
    inputs.ccm24.boundedComparisonMap g.placeSet ∧
      inputs.ccm24.boundedComparisonInverse g.placeSet :=
  g.ccm24RouteConsumerRows.boundedComparisonRows

theorem sonin_exhaustion_of_source_backed
    {inputs : RouteInputs} (g : SourceBackedFixedSTest inputs) :
    inputs.ccm24.fixedWindowExhaustionCompatible g.window :=
  g.ccm24RouteConsumerRows.fixedWindowExhaustionCompatible

theorem lambda_compatible_of_source_backed
    {inputs : RouteInputs} (g : SourceBackedFixedSTest inputs)
    {lambda : ℝ} (hlambda : 1 < lambda) :
    inputs.ccm24.lambdaCompatible g.window lambda :=
  g.ccm24RouteConsumerRows.lambdaCompatible lambda hlambda

theorem window_support_containment_of_source_backed
    {inputs : RouteInputs} (g : SourceBackedFixedSTest inputs)
    {lambda : ℝ} (hlambda : 1 < lambda) :
    WindowSupportContainment inputs g lambda :=
  ⟨g.ccm24RouteConsumerRows.supportInWindow,
    g.ccm24RouteConsumerRows.fourierSupportInWindow,
    g.ccm24RouteConsumerRows.convolutionSupportTransported,
    g.ccm24RouteConsumerRows.windowContainedInLambda lambda hlambda⟩

end Route
end ConnesWeilRH
