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

def FixedSProjectionDefectNormalFormForSourceRemainder
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  ∃ _row4 : ProjectionDefectNormalFormData inputs g lambda, True

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

def SourceRankPoleLedgerIdentification
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (L : RouteLedgers) : Prop :=
  ∃ lambda : ℝ,
    ∃ _row5 : RankPoleLedgerIdentificationData inputs g lambda L, True

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

def SourceEndpointStripRemainderCdefDomination
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (L : RouteLedgers) : Prop :=
  ∃ _row6 : EndpointStripCdefDominationData inputs g lambda L, True

def SourcePositiveTraceRemainderOwnership
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  CC20SourceRemainderOrientation inputs g ∧
    CC20SourceRemainderAfterQ inputs g ∧
      CC20PostQRemainderFixedSSoninTransport inputs g lambda

def TransportedSourceRemainderPartition
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (L : RouteLedgers) : Prop :=
  SourceRankPoleLedgerIdentification inputs g L ∧
    SourceEndpointStripRemainderCdefDomination inputs g lambda L

def EndpointStripRemainderBoundForRow7
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (L : RouteLedgers) : Prop :=
  SourceEndpointStripRemainderCdefDomination inputs g lambda L

def PositiveTraceToRestrictedLowerBound
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (L : RouteLedgers) : Prop :=
  SourceRankPoleLedgerIdentification inputs g L ∧
    SourceEndpointStripRemainderCdefDomination inputs g lambda L

structure NoHiddenPositiveDefectOutsideCdefData
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (L : RouteLedgers) where
  sourcePositiveTraceRemainderOwnership :
    SourcePositiveTraceRemainderOwnership inputs g lambda
  rankPoleLedgerIdentification :
    SourceRankPoleLedgerIdentification inputs g L
  endpointStripCdefDomination :
    SourceEndpointStripRemainderCdefDomination inputs g lambda L

def NoHiddenPositiveDefectOutsideCdef
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (L : RouteLedgers) : Prop :=
  ∃ _row7 : NoHiddenPositiveDefectOutsideCdefData inputs g lambda L, True

structure SourceSignDefectClassification
  (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
  (lambda : ℝ) (L : RouteLedgers) where
  oneLtLambda : 1 < lambda
  noHiddenPositiveDefect :
    NoHiddenPositiveDefectOutsideCdef inputs g lambda L

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
  h.noHiddenPositiveDefect.choose.sourcePositiveTraceRemainderOwnership.1

theorem source_remainder_after_q_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    CC20SourceRemainderAfterQ inputs g :=
  h.noHiddenPositiveDefect.choose.sourcePositiveTraceRemainderOwnership.2.1

theorem post_q_fixed_s_transport_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    CC20PostQRemainderFixedSSoninTransport inputs g lambda :=
  h.noHiddenPositiveDefect.choose.sourcePositiveTraceRemainderOwnership.2.2

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
  h.choose.sourceRemainderOwnership

theorem row4_no_strip_split_of_normal_form
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (h : FixedSProjectionDefectNormalFormForSourceRemainder inputs g lambda) :
    SourceRemainderNoStripProjectionSplit inputs g lambda :=
  h.choose.noStripProjectionSplit

theorem row4_endpoint_strip_of_normal_form
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (h : FixedSProjectionDefectNormalFormForSourceRemainder inputs g lambda) :
    SourceProjectionOrderEndpointStripNormalForm inputs g lambda :=
  h.choose.endpointStripNormalForm

theorem row4_classification_output_of_normal_form
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (h : FixedSProjectionDefectNormalFormForSourceRemainder inputs g lambda) :
    SourceRemainderRow4ClassificationOutput inputs g lambda :=
  ⟨h.choose.noStripProjectionSplit, h.choose.endpointStripNormalForm⟩

theorem row4_no_strip_split_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    SourceRemainderNoStripProjectionSplit inputs g lambda :=
  by
    let row6 :=
      h.noHiddenPositiveDefect.choose.endpointStripCdefDomination.choose
    exact row6.row4EndpointStripInput.1

theorem row4_endpoint_strip_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    SourceProjectionOrderEndpointStripNormalForm inputs g lambda :=
  by
    let row6 :=
      h.noHiddenPositiveDefect.choose.endpointStripCdefDomination.choose
    exact row6.row4EndpointStripInput

theorem row5_no_strip_channels_of_rank_pole_identification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (h : SourceRankPoleLedgerIdentification inputs g L) :
    ∃ lambda : ℝ, SourceNoStripChannelsForTransportedRemainder inputs g lambda :=
  ⟨h.choose, h.choose_spec.choose.row4NoStripInput⟩

theorem row5_rank_identification_of_rank_pole_identification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (h : SourceRankPoleLedgerIdentification inputs g L) :
    ∃ lambda : ℝ, SourceRankLedgerIdentification inputs g lambda L :=
  ⟨h.choose,
    ⟨h.choose_spec.choose.row4NoStripInput,
      h.choose_spec.choose.rankKilled⟩⟩

theorem row5_pole_identification_of_rank_pole_identification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (h : SourceRankPoleLedgerIdentification inputs g L) :
    ∃ lambda : ℝ, SourcePoleLedgerIdentification inputs g lambda L :=
  ⟨h.choose,
    ⟨h.choose_spec.choose.row4NoStripInput,
      h.choose_spec.choose.poleKilled⟩⟩

theorem row5_rank_ledger_of_rank_pole_identification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (h : SourceRankPoleLedgerIdentification inputs g L) :
    L.rankKilled :=
  h.choose_spec.choose.rankKilled

theorem row5_pole_ledger_of_rank_pole_identification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (h : SourceRankPoleLedgerIdentification inputs g L) :
    L.poleKilled :=
  h.choose_spec.choose.poleKilled

theorem row5_no_extra_no_strip_of_rank_pole_identification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (h : SourceRankPoleLedgerIdentification inputs g L) :
    ∃ lambda : ℝ, SourceNoExtraNoStripChannel inputs g lambda :=
  ⟨h.choose, h.choose_spec.choose.noExtraNoStripChannel⟩

theorem row5_ledger_vanishing_gate_of_rank_pole_identification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (h : SourceRankPoleLedgerIdentification inputs g L) :
    ∃ lambda : ℝ, SourceRankPoleLedgerVanishingGate inputs g lambda L :=
  ⟨h.choose,
    ⟨⟨h.choose_spec.choose.row4NoStripInput,
        h.choose_spec.choose.rankKilled⟩,
      ⟨⟨h.choose_spec.choose.row4NoStripInput,
          h.choose_spec.choose.poleKilled⟩,
        h.choose_spec.choose.noExtraNoStripChannel⟩⟩⟩

theorem row6_endpoint_terms_indexed_of_cdef_domination
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceEndpointStripRemainderCdefDomination inputs g lambda L) :
    SourceEndpointStripTermsCdefIndexed inputs g lambda :=
  ⟨h.choose.row4EndpointStripInput, h.choose.windowSupportContainment⟩

theorem row6_trace_norm_domination_of_cdef_domination
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceEndpointStripRemainderCdefDomination inputs g lambda L) :
    SourceEndpointStripTraceNormDomination inputs g lambda :=
  ⟨row6_endpoint_terms_indexed_of_cdef_domination h,
    h.choose.postQSeriesTailBoundedComparison⟩

theorem row6_remainder_bound_of_cdef_domination
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceEndpointStripRemainderCdefDomination inputs g lambda L) :
    SourceEndpointStripRemainderCdefBound inputs g lambda L :=
  ⟨row6_trace_norm_domination_of_cdef_domination h,
    h.choose.row5RankPoleRemovalInput⟩

theorem row6_fixed_test_cdef_exhaustion_of_cdef_domination
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceEndpointStripRemainderCdefDomination inputs g lambda L) :
    SourceEndpointStripFixedTestCdefExhaustion inputs g lambda L :=
  ⟨row6_remainder_bound_of_cdef_domination h,
    h.choose.windowSupportContainment,
    h.choose.cdefExhausts⟩

theorem row6_cdef_exhausts_of_cdef_domination
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceEndpointStripRemainderCdefDomination inputs g lambda L) :
    L.cdefExhausts :=
  h.choose.cdefExhausts

theorem row7_source_positive_trace_ownership_of_no_hidden_positive_defect
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : NoHiddenPositiveDefectOutsideCdef inputs g lambda L) :
    SourcePositiveTraceRemainderOwnership inputs g lambda :=
  h.choose.sourcePositiveTraceRemainderOwnership

theorem row7_transported_partition_of_no_hidden_positive_defect
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : NoHiddenPositiveDefectOutsideCdef inputs g lambda L) :
    TransportedSourceRemainderPartition inputs g lambda L :=
  ⟨h.choose.rankPoleLedgerIdentification,
    h.choose.endpointStripCdefDomination⟩

theorem row7_endpoint_strip_bound_of_no_hidden_positive_defect
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : NoHiddenPositiveDefectOutsideCdef inputs g lambda L) :
    EndpointStripRemainderBoundForRow7 inputs g lambda L :=
  h.choose.endpointStripCdefDomination

theorem row7_positive_trace_to_lower_bound_of_no_hidden_positive_defect
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : NoHiddenPositiveDefectOutsideCdef inputs g lambda L) :
    PositiveTraceToRestrictedLowerBound inputs g lambda L :=
  ⟨h.choose.rankPoleLedgerIdentification,
    h.choose.endpointStripCdefDomination⟩

theorem row7_rank_pole_identification_of_no_hidden_positive_defect
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : NoHiddenPositiveDefectOutsideCdef inputs g lambda L) :
    SourceRankPoleLedgerIdentification inputs g L :=
  h.choose.rankPoleLedgerIdentification

theorem row7_endpoint_strip_cdef_domination_of_no_hidden_positive_defect
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : NoHiddenPositiveDefectOutsideCdef inputs g lambda L) :
    SourceEndpointStripRemainderCdefDomination inputs g lambda L :=
  h.choose.endpointStripCdefDomination

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
    SourceRankPoleLedgerIdentification inputs g L :=
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
