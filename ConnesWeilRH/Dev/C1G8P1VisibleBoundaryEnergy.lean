import ConnesWeilRH.Dev.C1G8P1BoundaryEnergyExtension
import ConnesWeilRH.Dev.C1G8P1MetricChannels

/-!
# G8 P1 visible-boundary coframe energy

The metric survivor/boundary telescope gives a concrete finite-Euler boundary
coframe.  This leaf records that the coframe remains Hilbert--Schmidt after
the genuine source-prolate factor is pulled back to the source Sonin carrier.
It is a finite-cutoff P1 energy fact only: no radial identification, scalar
prime-power readback, endpoint limit, or `qw` sign is asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1VisibleBoundaryEnergy

open CCM25Concrete
open CC20Concrete
open CCM25Concrete.CCM24FiniteSGramResponse
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24SourceProlateTrace
open C1G8P1MetricChannels
open CC20Concrete.PositiveTrace
open scoped InnerProduct InnerProductSpace

noncomputable section

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

theorem g8MetricVisibleBoundaryCoframe_comp_summable_normSq
    {ι K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis ι ℂ K)
    (input : K →L[ℂ] sourceSoninCarrier lambda)
    (hinput : Summable fun i => ‖input (sourceBasis i)‖ ^ 2) :
    Summable fun i =>
      ‖(g8MetricVisibleBoundaryCoframe lambda family ∘L input)
          (sourceBasis i)‖ ^ 2 := by
  exact PositiveTrace.summable_normSq_postcomp sourceBasis input
    (g8MetricVisibleBoundaryCoframe lambda family) hinput

theorem g8MetricVisibleBoundaryCoframe_comp_sourceProlateFactor_summable_normSq
    {nu rho : Type*}
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    Summable fun i =>
      ‖(g8MetricVisibleBoundaryCoframe lambda family ∘L
          ((sourceInclusion lambda)† ∘L
            sourceProlateHilbertSchmidtFactor lambda ∘L
              sourceInclusion lambda)) (sourceBasis i)‖ ^ 2 := by
  let factor := sourceProlateHilbertSchmidtFactor lambda
  let inclusion := sourceInclusion lambda
  let inclusionAdj := inclusion†
  let input : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
    inclusionAdj ∘L factor ∘L inclusion
  have hpre : Summable fun i =>
      ‖(factor ∘L inclusion) (sourceBasis i)‖ ^ 2 := by
    exact summable_normSq_precomp globalBasis globalBasis sourceBasis
      factor inclusion hfactor
  have hinclusionAdj : ‖inclusionAdj‖ ≤ (1 : ℝ) := by
    calc
      ‖inclusionAdj‖ = ‖inclusion‖ := by
        exact ContinuousLinearMap.adjoint.norm_map inclusion
      _ ≤ 1 := Submodule.norm_subtypeL_le _
  have hinput : Summable fun i => ‖input (sourceBasis i)‖ ^ 2 := by
    apply Summable.of_nonneg_of_le
      (fun i => sq_nonneg _)
      (fun i => ?_)
      (hpre.mul_left (‖inclusionAdj‖ ^ 2))
    simp only [input, ContinuousLinearMap.comp_apply]
    calc
      ‖inclusionAdj ((factor ∘L inclusion) (sourceBasis i))‖ ^ 2 ≤
          (‖inclusionAdj‖ * ‖(factor ∘L inclusion) (sourceBasis i)‖) ^ 2 := by
        gcongr
        exact inclusionAdj.le_opNorm _
      _ = ‖inclusionAdj‖ ^ 2 *
          ‖(factor ∘L inclusion) (sourceBasis i)‖ ^ 2 := by ring
  simpa only [input, factor, inclusion, ContinuousLinearMap.comp_apply] using
    (g8MetricVisibleBoundaryCoframe_comp_summable_normSq lambda family
      sourceBasis input hinput)

end
end C1G8P1VisibleBoundaryEnergy
end Source
end ConnesWeilRH
