import ConnesWeilRH.Dev.CCM24FiniteSEndpointResidualProbe
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCanonicalAdjointEnergyGate
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCombinedPhysicalEnergyGate
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSPhysicalCancellationEndpointNormalForm
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCoframeResponse

namespace ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSEndpointResidualProbe

#check sourceEndpointCancellationResidual
#check sourceEndpointCancellationResidual_eq_offSonin_sum
#check sourceEndpointCancellationResidual_band_sum_gap
#check sourceEndpointCancellationResidual_eq_outer_add_forward_add_bandMetric
#check sourceOuterCoframeLeakage_eq_radial_support_comp_metricCoframe
#check sourceEndpointCancellationResidual_eq_outer_add_endpointBand
#check sourceActualBandForwardEndpointCoframe_eq_inclusion_iff_combined_leakage_eq_zero
#check radialSupportProjection_comp_finiteEulerDualFrame
#check sourceOuterCoframeLeakage_eq_radialComp_comp_transportAdjoint_comp_dualFrame
#check norm_finiteEulerTransportAdjoint_le_upperFactor
#check radialSupport_comp_transportAdjoint_comp_radialComplement

/-! ### Route-2 feasibility probe (2026-08-05, no new theorem)

The Gate closer `canonicalRealGate3UAt_of_completedKernelRightEnergy` wants
`sourcePhysicalCoframeCompletedKernelRightEnergy ≤ fixedPhysicalEnergyMajorant`,
which is a footprint of `right ∘ physicalLeakage` along the source basis.  The
in-library contraction bound (contraction:50) instead majors
`right ∘ (forward+metric)` = `right ∘ endpoint`.  The only in-library handshake
`physicalLeakage = residual − forward` re-links the two footprints through the
same metric wall `residual = 0`.  These #checks pin the three objects so Route 3
can anchor on the exact open premise (the transport-adjoint radial defect). -/
#check ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCanonicalAdjointEnergyGate.sourcePhysicalCoframeCompletedKernelRightEnergy
#check ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCombinedPhysicalEnergyGate.sourceActualBandCombinedPhysicalRightEnergy
#check ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSPhysicalCancellationEndpointNormalForm.sourceEndpointCancellationResidual_eq_forward_add_physicalLeakage

/-! ### Route-A negative probe (2026-08-05, no new theorem)

The dual frame `D = F ∘ G⁻¹` (`finiteEulerGramInv` is self-adjoint but has no
HS / decay / diagonal facts).  These resolve so Route 3 can be explored, but
they do NOT yet give `∑' ‖D·b‖²` or `∑' ‖finiteEulerMetricCoframe b‖²`
finiteness for the source basis. -/
#check ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGramResponse.finiteEulerDualFrame
#check ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCoframeResponse.finiteEulerMetricCoframe
#check ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGramResponse.finiteEulerGramInv

#print axioms sourceEndpointCancellationResidual_eq_offSonin_sum
#print axioms sourceEndpointCancellationResidual_band_sum_gap
#print axioms sourceEndpointCancellationResidual_eq_outer_add_forward_add_bandMetric
#print axioms sourceOuterCoframeLeakage_eq_radial_support_comp_metricCoframe
#print axioms sourceEndpointCancellationResidual_eq_outer_add_endpointBand
#print axioms sourceActualBandForwardEndpointCoframe_eq_inclusion_iff_combined_leakage_eq_zero
#print axioms radialSupportProjection_comp_finiteEulerDualFrame
#print axioms sourceOuterCoframeLeakage_eq_radialComp_comp_transportAdjoint_comp_dualFrame
#print axioms norm_finiteEulerTransportAdjoint_le_upperFactor
#print axioms radialSupport_comp_transportAdjoint_comp_radialComplement

end ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSEndpointResidualProbe
