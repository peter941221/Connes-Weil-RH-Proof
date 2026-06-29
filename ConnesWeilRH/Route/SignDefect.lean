/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Route.AdmissibleWindow

/-!
# Sign/defect contract

This module exposes the hard Rows 1--7 sign/defect chain as Lean data.  It does
not prove the analytic rows.  It prevents the route from replacing the chain by
a bare `rankKilled ∧ poleKilled ∧ cdefExhausts` assertion.
-/

namespace ConnesWeilRH
namespace Route

def CC20SourceRemainderOrientation
    (_inputs : RouteInputs) (_g : SourceBackedFixedSTest _inputs) : Prop :=
  (Source.cc20SignsAndNormalizations _inputs.cc20.archimedeanSymbols).Holds

def CC20SourceRemainderAfterQ
    (_inputs : RouteInputs) (_g : SourceBackedFixedSTest _inputs) : Prop :=
  (Source.cc20MellinHalfDensityConvention
      _inputs.cc20.archimedeanSymbols).Holds

def PostQDerivativeDomainCompatibility
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  WindowSupportContainment inputs g lambda

def PostQBoundaryEvaluationTransport
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  inputs.ccm24.semilocalSymbols.lambdaCompatible g.window lambda

def PostQSeriesTailBoundedComparison
    (inputs : RouteInputs) (_g : SourceBackedFixedSTest inputs)
    (_lambda : ℝ) : Prop :=
  (Source.ccm24BoundedComparison inputs.ccm24.semilocalSymbols).Holds ∧
    (Source.ccm24SoninComparison inputs.ccm24.semilocalSymbols).Holds

def CC20PostQTermwiseFixedSTransport
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  PostQDerivativeDomainCompatibility inputs g lambda ∧
    PostQBoundaryEvaluationTransport inputs g lambda

def CC20PostQSeriesTailTransport
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  PostQSeriesTailBoundedComparison inputs g lambda

def CC20PostQRemainderFixedSSoninTransport
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  CC20SourceRemainderAfterQ inputs g ∧
    CC20PostQTermwiseFixedSTransport inputs g lambda ∧
      CC20PostQSeriesTailTransport inputs g lambda

def SourceRemainderOwnershipForProjectionDefectRow
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  CC20PostQRemainderFixedSSoninTransport inputs g lambda

def SourceRemainderNoStripProjectionSplit
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  SourceRemainderOwnershipForProjectionDefectRow inputs g lambda ∧
    inputs.ccm24.semilocalSymbols.lambdaCompatible g.window lambda

def SourceProjectionOrderEndpointStripNormalForm
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  SourceRemainderNoStripProjectionSplit inputs g lambda ∧
    (Source.ccm24SoninComparison inputs.ccm24.semilocalSymbols).Holds

def SourceRemainderRow4ClassificationOutput
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  SourceRemainderNoStripProjectionSplit inputs g lambda ∧
    SourceProjectionOrderEndpointStripNormalForm inputs g lambda

structure ProjectionDefectNormalFormData
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) where
  sourceRemainderOwnership :
    SourceRemainderOwnershipForProjectionDefectRow inputs g lambda
  noStripProjectionSplit :
    SourceRemainderNoStripProjectionSplit inputs g lambda
  endpointStripNormalForm :
    SourceProjectionOrderEndpointStripNormalForm inputs g lambda

def projection_defect_normal_form_data_of_parts
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (hownership :
      SourceRemainderOwnershipForProjectionDefectRow inputs g lambda)
    (hnoStrip :
      SourceRemainderNoStripProjectionSplit inputs g lambda)
    (hendpoint :
      SourceProjectionOrderEndpointStripNormalForm inputs g lambda) :
    ProjectionDefectNormalFormData inputs g lambda where
  sourceRemainderOwnership := hownership
  noStripProjectionSplit := hnoStrip
  endpointStripNormalForm := hendpoint

abbrev FixedSProjectionDefectNormalFormForSourceRemainder
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) :=
  ProjectionDefectNormalFormData inputs g lambda

def fixed_s_projection_defect_normal_form_of_parts
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (hownership :
      SourceRemainderOwnershipForProjectionDefectRow inputs g lambda)
    (hnoStrip :
      SourceRemainderNoStripProjectionSplit inputs g lambda)
    (hendpoint :
      SourceProjectionOrderEndpointStripNormalForm inputs g lambda) :
    FixedSProjectionDefectNormalFormForSourceRemainder inputs g lambda :=
  projection_defect_normal_form_data_of_parts
    hownership hnoStrip hendpoint

def SourceNoStripChannelsForTransportedRemainder
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  SourceRemainderNoStripProjectionSplit inputs g lambda

def SourceRankLedgerIdentification
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (L : RouteLedgers) : Prop :=
  SourceNoStripChannelsForTransportedRemainder inputs g lambda ∧
    L.rankKilled

def SourcePoleLedgerIdentification
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (L : RouteLedgers) : Prop :=
  SourceNoStripChannelsForTransportedRemainder inputs g lambda ∧
    L.poleKilled

def SourceNoExtraNoStripChannel
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  SourceRemainderRow4ClassificationOutput inputs g lambda

def SourceRankPoleLedgerVanishingGate
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (L : RouteLedgers) : Prop :=
  SourceRankLedgerIdentification inputs g lambda L ∧
    SourcePoleLedgerIdentification inputs g lambda L ∧
      SourceNoExtraNoStripChannel inputs g lambda

structure RankPoleLedgerIdentificationData
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (L : RouteLedgers) where
  row4NoStripInput :
    SourceRemainderNoStripProjectionSplit inputs g lambda
  noExtraNoStripChannel :
    SourceNoExtraNoStripChannel inputs g lambda
  rankKilled : L.rankKilled
  poleKilled : L.poleKilled

def rank_pole_ledger_identification_data_of_parts
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (hnoStrip :
      SourceRemainderNoStripProjectionSplit inputs g lambda)
    (hnoExtra :
      SourceNoExtraNoStripChannel inputs g lambda)
    (hrank : L.rankKilled)
    (hpole : L.poleKilled) :
    RankPoleLedgerIdentificationData inputs g lambda L where
  row4NoStripInput := hnoStrip
  noExtraNoStripChannel := hnoExtra
  rankKilled := hrank
  poleKilled := hpole

abbrev SourceRankPoleLedgerIdentification
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (L : RouteLedgers) :=
  RankPoleLedgerIdentificationData inputs g lambda L

def source_rank_pole_ledger_identification_of_parts
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (hnoStrip :
      SourceRemainderNoStripProjectionSplit inputs g lambda)
    (hnoExtra :
      SourceNoExtraNoStripChannel inputs g lambda)
    (hrank : L.rankKilled)
    (hpole : L.poleKilled) :
    SourceRankPoleLedgerIdentification inputs g lambda L :=
  rank_pole_ledger_identification_data_of_parts
    hnoStrip hnoExtra hrank hpole

def SourceEndpointStripTermsCdefIndexed
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  SourceProjectionOrderEndpointStripNormalForm inputs g lambda ∧
    WindowSupportContainment inputs g lambda

def SourceEndpointStripTraceNormDomination
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  SourceEndpointStripTermsCdefIndexed inputs g lambda ∧
    PostQSeriesTailBoundedComparison inputs g lambda

def SourceEndpointStripRemainderCdefBound
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (L : RouteLedgers) : Prop :=
  SourceEndpointStripTraceNormDomination inputs g lambda ∧
    SourceRankPoleLedgerVanishingGate inputs g lambda L

def SourceEndpointStripFixedTestCdefExhaustion
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (L : RouteLedgers) : Prop :=
  SourceEndpointStripRemainderCdefBound inputs g lambda L ∧
    WindowSupportContainment inputs g lambda ∧
      L.cdefExhausts

structure EndpointStripCdefDominationData
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (L : RouteLedgers) where
  row4EndpointStripInput :
    SourceProjectionOrderEndpointStripNormalForm inputs g lambda
  windowSupportContainment :
    WindowSupportContainment inputs g lambda
  postQSeriesTailBoundedComparison :
    PostQSeriesTailBoundedComparison inputs g lambda
  row5RankPoleRemovalInput :
    SourceRankPoleLedgerVanishingGate inputs g lambda L
  cdefExhausts : L.cdefExhausts

def endpoint_strip_cdef_domination_data_of_parts
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (hendpoint :
      SourceProjectionOrderEndpointStripNormalForm inputs g lambda)
    (hwindow : WindowSupportContainment inputs g lambda)
    (htail : PostQSeriesTailBoundedComparison inputs g lambda)
    (hrankPole :
      SourceRankPoleLedgerVanishingGate inputs g lambda L)
    (hcdef : L.cdefExhausts) :
    EndpointStripCdefDominationData inputs g lambda L where
  row4EndpointStripInput := hendpoint
  windowSupportContainment := hwindow
  postQSeriesTailBoundedComparison := htail
  row5RankPoleRemovalInput := hrankPole
  cdefExhausts := hcdef

abbrev SourceEndpointStripRemainderCdefDomination
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (L : RouteLedgers) :=
  EndpointStripCdefDominationData inputs g lambda L

def source_endpoint_strip_remainder_cdef_domination_of_parts
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (hendpoint :
      SourceProjectionOrderEndpointStripNormalForm inputs g lambda)
    (hwindow : WindowSupportContainment inputs g lambda)
    (htail : PostQSeriesTailBoundedComparison inputs g lambda)
    (hrankPole :
      SourceRankPoleLedgerVanishingGate inputs g lambda L)
    (hcdef : L.cdefExhausts) :
    SourceEndpointStripRemainderCdefDomination inputs g lambda L :=
  endpoint_strip_cdef_domination_data_of_parts
    hendpoint hwindow htail hrankPole hcdef

def SourcePositiveTraceRemainderOwnership
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  CC20SourceRemainderOrientation inputs g ∧
    CC20SourceRemainderAfterQ inputs g ∧
      CC20PostQRemainderFixedSSoninTransport inputs g lambda

structure TransportedSourceRemainderPartition
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (L : RouteLedgers) where
  rankPoleLedgerIdentification :
    SourceRankPoleLedgerIdentification inputs g lambda L
  endpointStripCdefDomination :
    SourceEndpointStripRemainderCdefDomination inputs g lambda L

abbrev EndpointStripRemainderBoundForRow7
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (L : RouteLedgers) :=
  SourceEndpointStripRemainderCdefDomination inputs g lambda L

structure PositiveTraceToRestrictedLowerBound
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (L : RouteLedgers) where
  rankPoleLedgerIdentification :
    SourceRankPoleLedgerIdentification inputs g lambda L
  endpointStripCdefDomination :
    SourceEndpointStripRemainderCdefDomination inputs g lambda L

structure NoHiddenPositiveDefectOutsideCdefData
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (L : RouteLedgers) where
  sourcePositiveTraceRemainderOwnership :
    SourcePositiveTraceRemainderOwnership inputs g lambda
  rankPoleLedgerIdentification :
    SourceRankPoleLedgerIdentification inputs g lambda L
  endpointStripCdefDomination :
    SourceEndpointStripRemainderCdefDomination inputs g lambda L

def no_hidden_positive_defect_data_of_parts
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (hownership :
      SourcePositiveTraceRemainderOwnership inputs g lambda)
    (hrankPole : SourceRankPoleLedgerIdentification inputs g lambda L)
    (hcdef :
      SourceEndpointStripRemainderCdefDomination inputs g lambda L) :
    NoHiddenPositiveDefectOutsideCdefData inputs g lambda L where
  sourcePositiveTraceRemainderOwnership := hownership
  rankPoleLedgerIdentification := hrankPole
  endpointStripCdefDomination := hcdef

abbrev NoHiddenPositiveDefectOutsideCdef
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (L : RouteLedgers) :=
  NoHiddenPositiveDefectOutsideCdefData inputs g lambda L

def no_hidden_positive_defect_outside_cdef_of_parts
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (hownership :
      SourcePositiveTraceRemainderOwnership inputs g lambda)
    (hrankPole : SourceRankPoleLedgerIdentification inputs g lambda L)
    (hcdef :
      SourceEndpointStripRemainderCdefDomination inputs g lambda L) :
    NoHiddenPositiveDefectOutsideCdef inputs g lambda L :=
  no_hidden_positive_defect_data_of_parts
    hownership hrankPole hcdef

structure SourceSignDefectClassification
  (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
  (lambda : ℝ) (L : RouteLedgers) where
  oneLtLambda : 1 < lambda
  noHiddenPositiveDefect :
    NoHiddenPositiveDefectOutsideCdef inputs g lambda L

def source_sign_defect_classification_of_parts
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (hlambda : 1 < lambda)
    (hnoHidden :
      NoHiddenPositiveDefectOutsideCdef inputs g lambda L) :
    SourceSignDefectClassification inputs g lambda L where
  oneLtLambda := hlambda
  noHiddenPositiveDefect := hnoHidden

theorem post_q_fixed_s_transport_of_subcontracts
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (hAfterQ : CC20SourceRemainderAfterQ inputs g)
    (hTermwise : CC20PostQTermwiseFixedSTransport inputs g lambda)
    (hTail : CC20PostQSeriesTailTransport inputs g lambda) :
    CC20PostQRemainderFixedSSoninTransport inputs g lambda :=
  ⟨hAfterQ, hTermwise, hTail⟩

theorem source_orientation_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    CC20SourceRemainderOrientation inputs g :=
  h.noHiddenPositiveDefect.sourcePositiveTraceRemainderOwnership.1

theorem source_remainder_after_q_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    CC20SourceRemainderAfterQ inputs g :=
  h.noHiddenPositiveDefect.sourcePositiveTraceRemainderOwnership.2.1

theorem post_q_fixed_s_transport_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    CC20PostQRemainderFixedSSoninTransport inputs g lambda :=
  h.noHiddenPositiveDefect.sourcePositiveTraceRemainderOwnership.2.2

theorem post_q_derivative_domain_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    PostQDerivativeDomainCompatibility inputs g lambda :=
  (post_q_fixed_s_transport_of_sign_defect_classification h).2.1.1

theorem post_q_boundary_transport_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    PostQBoundaryEvaluationTransport inputs g lambda :=
  (post_q_fixed_s_transport_of_sign_defect_classification h).2.1.2

theorem post_q_series_tail_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    PostQSeriesTailBoundedComparison inputs g lambda :=
  (post_q_fixed_s_transport_of_sign_defect_classification h).2.2

theorem row4_ownership_of_normal_form
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (h : FixedSProjectionDefectNormalFormForSourceRemainder inputs g lambda) :
    SourceRemainderOwnershipForProjectionDefectRow inputs g lambda :=
  h.sourceRemainderOwnership

theorem row4_no_strip_split_of_normal_form
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (h : FixedSProjectionDefectNormalFormForSourceRemainder inputs g lambda) :
    SourceRemainderNoStripProjectionSplit inputs g lambda :=
  h.noStripProjectionSplit

theorem row4_endpoint_strip_of_normal_form
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (h : FixedSProjectionDefectNormalFormForSourceRemainder inputs g lambda) :
    SourceProjectionOrderEndpointStripNormalForm inputs g lambda :=
  h.endpointStripNormalForm

theorem row4_classification_output_of_normal_form
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (h : FixedSProjectionDefectNormalFormForSourceRemainder inputs g lambda) :
    SourceRemainderRow4ClassificationOutput inputs g lambda :=
  ⟨h.noStripProjectionSplit, h.endpointStripNormalForm⟩

theorem row4_no_strip_split_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    SourceRemainderNoStripProjectionSplit inputs g lambda :=
  h.noHiddenPositiveDefect.endpointStripCdefDomination.row4EndpointStripInput.1

theorem row4_endpoint_strip_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    SourceProjectionOrderEndpointStripNormalForm inputs g lambda :=
  h.noHiddenPositiveDefect.endpointStripCdefDomination.row4EndpointStripInput

theorem row5_no_strip_channels_of_rank_pole_identification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceRankPoleLedgerIdentification inputs g lambda L) :
    SourceNoStripChannelsForTransportedRemainder inputs g lambda :=
  h.row4NoStripInput

theorem row5_rank_identification_of_rank_pole_identification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceRankPoleLedgerIdentification inputs g lambda L) :
    SourceRankLedgerIdentification inputs g lambda L :=
  ⟨h.row4NoStripInput, h.rankKilled⟩

theorem row5_pole_identification_of_rank_pole_identification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceRankPoleLedgerIdentification inputs g lambda L) :
    SourcePoleLedgerIdentification inputs g lambda L :=
  ⟨h.row4NoStripInput, h.poleKilled⟩

theorem row5_rank_ledger_of_rank_pole_identification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceRankPoleLedgerIdentification inputs g lambda L) :
    L.rankKilled :=
  h.rankKilled

theorem row5_pole_ledger_of_rank_pole_identification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceRankPoleLedgerIdentification inputs g lambda L) :
    L.poleKilled :=
  h.poleKilled

theorem row5_no_extra_no_strip_of_rank_pole_identification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceRankPoleLedgerIdentification inputs g lambda L) :
    SourceNoExtraNoStripChannel inputs g lambda :=
  h.noExtraNoStripChannel

theorem row5_ledger_vanishing_gate_of_rank_pole_identification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceRankPoleLedgerIdentification inputs g lambda L) :
    SourceRankPoleLedgerVanishingGate inputs g lambda L :=
  ⟨⟨h.row4NoStripInput, h.rankKilled⟩,
    ⟨⟨h.row4NoStripInput, h.poleKilled⟩,
      h.noExtraNoStripChannel⟩⟩

theorem row6_endpoint_terms_indexed_of_cdef_domination
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceEndpointStripRemainderCdefDomination inputs g lambda L) :
    SourceEndpointStripTermsCdefIndexed inputs g lambda :=
  ⟨h.row4EndpointStripInput, h.windowSupportContainment⟩

theorem row6_trace_norm_domination_of_cdef_domination
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceEndpointStripRemainderCdefDomination inputs g lambda L) :
    SourceEndpointStripTraceNormDomination inputs g lambda :=
  ⟨row6_endpoint_terms_indexed_of_cdef_domination h,
    h.postQSeriesTailBoundedComparison⟩

theorem row6_remainder_bound_of_cdef_domination
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceEndpointStripRemainderCdefDomination inputs g lambda L) :
    SourceEndpointStripRemainderCdefBound inputs g lambda L :=
  ⟨row6_trace_norm_domination_of_cdef_domination h,
    h.row5RankPoleRemovalInput⟩

theorem row6_fixed_test_cdef_exhaustion_of_cdef_domination
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceEndpointStripRemainderCdefDomination inputs g lambda L) :
    SourceEndpointStripFixedTestCdefExhaustion inputs g lambda L :=
  ⟨row6_remainder_bound_of_cdef_domination h,
    h.windowSupportContainment,
    h.cdefExhausts⟩

theorem row6_cdef_exhausts_of_cdef_domination
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceEndpointStripRemainderCdefDomination inputs g lambda L) :
    L.cdefExhausts :=
  h.cdefExhausts

theorem row7_source_positive_trace_ownership_of_no_hidden_positive_defect
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : NoHiddenPositiveDefectOutsideCdef inputs g lambda L) :
    SourcePositiveTraceRemainderOwnership inputs g lambda :=
  h.sourcePositiveTraceRemainderOwnership

theorem row7_transported_partition_of_no_hidden_positive_defect
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : NoHiddenPositiveDefectOutsideCdef inputs g lambda L) :
    TransportedSourceRemainderPartition inputs g lambda L :=
  { rankPoleLedgerIdentification := h.rankPoleLedgerIdentification
    endpointStripCdefDomination := h.endpointStripCdefDomination }

theorem row7_endpoint_strip_bound_of_no_hidden_positive_defect
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : NoHiddenPositiveDefectOutsideCdef inputs g lambda L) :
    EndpointStripRemainderBoundForRow7 inputs g lambda L :=
  h.endpointStripCdefDomination

theorem row7_positive_trace_to_lower_bound_of_no_hidden_positive_defect
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : NoHiddenPositiveDefectOutsideCdef inputs g lambda L) :
    PositiveTraceToRestrictedLowerBound inputs g lambda L :=
  { rankPoleLedgerIdentification := h.rankPoleLedgerIdentification
    endpointStripCdefDomination := h.endpointStripCdefDomination }

theorem row7_rank_pole_identification_of_no_hidden_positive_defect
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : NoHiddenPositiveDefectOutsideCdef inputs g lambda L) :
    SourceRankPoleLedgerIdentification inputs g lambda L :=
  h.rankPoleLedgerIdentification

theorem row7_endpoint_strip_cdef_domination_of_no_hidden_positive_defect
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : NoHiddenPositiveDefectOutsideCdef inputs g lambda L) :
    SourceEndpointStripRemainderCdefDomination inputs g lambda L :=
  h.endpointStripCdefDomination

theorem row7_source_positive_trace_ownership_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    SourcePositiveTraceRemainderOwnership inputs g lambda :=
  row7_source_positive_trace_ownership_of_no_hidden_positive_defect
    h.noHiddenPositiveDefect

theorem row7_transported_partition_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    TransportedSourceRemainderPartition inputs g lambda L :=
  row7_transported_partition_of_no_hidden_positive_defect
    h.noHiddenPositiveDefect

theorem row7_endpoint_strip_bound_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    EndpointStripRemainderBoundForRow7 inputs g lambda L :=
  row7_endpoint_strip_bound_of_no_hidden_positive_defect
    h.noHiddenPositiveDefect

theorem row7_rank_pole_identification_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    SourceRankPoleLedgerIdentification inputs g lambda L :=
  row7_rank_pole_identification_of_no_hidden_positive_defect
    h.noHiddenPositiveDefect

theorem row7_endpoint_strip_cdef_domination_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    SourceEndpointStripRemainderCdefDomination inputs g lambda L :=
  row7_endpoint_strip_cdef_domination_of_no_hidden_positive_defect
    h.noHiddenPositiveDefect

theorem rank_killed_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    L.rankKilled :=
  row5_rank_ledger_of_rank_pole_identification
    (row7_rank_pole_identification_of_sign_defect_classification h)

theorem pole_killed_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    L.poleKilled :=
  row5_pole_ledger_of_rank_pole_identification
    (row7_rank_pole_identification_of_sign_defect_classification h)

theorem cdef_exhausts_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    L.cdefExhausts :=
  row6_cdef_exhausts_of_cdef_domination
    (row7_endpoint_strip_cdef_domination_of_sign_defect_classification h)

theorem positive_trace_to_restricted_lower_bound_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    PositiveTraceToRestrictedLowerBound inputs g lambda L :=
  row7_positive_trace_to_lower_bound_of_no_hidden_positive_defect
    h.noHiddenPositiveDefect

theorem ledgers_cleared_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    L.rankKilled ∧ L.poleKilled ∧ L.cdefExhausts :=
  ⟨rank_killed_of_sign_defect_classification h,
    pole_killed_of_sign_defect_classification h,
    cdef_exhausts_of_sign_defect_classification h⟩

end Route
end ConnesWeilRH
