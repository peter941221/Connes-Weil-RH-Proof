/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20YoshidaCriterion

/-!
# CC20 Proposition C.1, parameterized by concrete detector existence

This module supplies the clean formal route from route positivity data to
`RHDefinitionBridge.standard.SourceRH`, assuming a concrete CC20 test-space
owner has already proved Yoshida detector existence.
-/

namespace ConnesWeilRH
namespace Source

theorem cc20_proposition_c1_standard_source_criterion_of_yoshida_detectors
    (C : CC20TestSpace)
    (hexists :
      CC20YoshidaDetectorExists C cc20TripleFiniteVanishingSet)
    (hrealize :
      ∀ input : WeilPositivityInput,
        CC20RouteInputRealizesFiniteVanishingCriterion
          C cc20TripleFiniteVanishingSet input) :
    ∀ input : WeilPositivityInput,
      CC20PropositionC1InputData
        RHDefinitionBridge.standard
        cc20TripleFiniteVanishingSet
        input →
      RHDefinitionBridge.standard.SourceRH := by
  intro input hdata
  exact
    cc20_proposition_c1_from_yoshida_detector
      C
      cc20TripleFiniteVanishingSet
      cc20_triple_finite_set_admissibility
      hdata.finiteSetDisjointFromNontrivialZeros
      hexists
      ((hrealize input).routeInputIsCC20Criterion
        hdata.fullWeilPositivity)

theorem cc20_proposition_c1_standard_source_rh_of_realized_input
    (C : CC20TestSpace)
    (F : Finset CriticalVanishingPoint)
    (hfinite : SourceFiniteSetAdmissibility F)
    (hexists : CC20YoshidaDetectorExists C F)
    {input : WeilPositivityInput}
    (hrealize :
      CC20RouteInputRealizesFiniteVanishingCriterion C F input)
    (hdata :
      CC20PropositionC1InputData RHDefinitionBridge.standard F input) :
    RHDefinitionBridge.standard.SourceRH :=
  cc20_proposition_c1_from_yoshida_detector
    C F hfinite hdata.finiteSetDisjointFromNontrivialZeros hexists
    (hrealize.routeInputIsCC20Criterion hdata.fullWeilPositivity)

theorem cc20_proposition_c1_standard_source_rh_of_realized_cc20_triple_input
    (C : CC20TestSpace)
    (hexists :
      CC20YoshidaDetectorExists C cc20TripleFiniteVanishingSet)
    {input : WeilPositivityInput}
    (hrealize :
      CC20RouteInputRealizesFiniteVanishingCriterion
        C cc20TripleFiniteVanishingSet input)
    (hdata :
      CC20PropositionC1InputData
        RHDefinitionBridge.standard
        cc20TripleFiniteVanishingSet input) :
    RHDefinitionBridge.standard.SourceRH :=
  cc20_proposition_c1_standard_source_rh_of_realized_input
    C cc20TripleFiniteVanishingSet
    cc20_triple_finite_set_admissibility hexists hrealize hdata

end Source
end ConnesWeilRH
