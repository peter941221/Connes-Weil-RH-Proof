import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSchurPolarTelescoping
import ConnesWeilRH.Dev.C1G8P1MetricChannels

/-!
# G8 P1 local boundary orthogonality

Each Schur boundary dagger lands in the orthogonal complement of the
corresponding new-frame range.  This is the exact geometric fact needed when
separating survivor and boundary channels; it does not identify the boundary
with a radial prime-power crossing.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1BoundaryOrthogonality

open CCM25Concrete
open CC20Concrete
open CCM25Concrete.CCM24FiniteSActualSchurCascade
open CCM25Concrete.CCM24FiniteSFrameGramCalculus
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSSchurPolarTelescoping
open CCM25Concrete.CCM24FiniteSFixedSourcePolar
open CCM25Concrete.CCM24FiniteSTransportBounds
open C1G8P1MetricChannels
open scoped InnerProduct InnerProductSpace

noncomputable section

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

theorem suffixEulerFrameSchurStep_newFrame_adjoint_comp_boundaryDagger_eq_zero
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ContinuousLinearMap.adjoint (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
        (suffixEulerFrameSchurStep lambda p S).boundaryDagger = 0 := by
  let step := suffixEulerFrameSchurStep lambda p S
  apply ContinuousLinearMap.ext
  intro x
  change (ContinuousLinearMap.adjoint step.newFrame)
      ((ContinuousLinearMap.id ℂ finiteSCarrier -
          step.newFrame ∘L ContinuousLinearMap.adjoint step.newFrame)
        (ContinuousLinearMap.adjoint step.transport (step.oldFrame x))) = 0
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply]
  have hiso := DFunLike.congr_fun step.newFrame_isometry
    ((ContinuousLinearMap.adjoint step.newFrame)
      ((ContinuousLinearMap.adjoint step.transport) (step.oldFrame x)))
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hiso
  rw [map_sub, hiso]
  simp

theorem suffixEulerTerminalFrame_adjoint_comp_boundarySum_eq_zero
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    ContinuousLinearMap.adjoint (newSuffixFrame lambda []) ∘L
        (suffixEulerBoundaryOutputMaps lambda S).sum = 0 := by
  let terminal := newSuffixFrame lambda []
  let ambient := suffixEulerAmbientProduct S
  let finalFrame := newSuffixFrame lambda S
  let transition := suffixEulerTransitionProduct lambda S
  have hterminal : ContinuousLinearMap.adjoint terminal ∘L terminal =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
    simpa only [terminal, newSuffixFrame] using
      (parameterizedSoninPolarFrame_adjoint_comp_self lambda 1 [] (by norm_num))
  have hfinal : ContinuousLinearMap.adjoint finalFrame ∘L finalFrame =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
    simpa only [finalFrame, newSuffixFrame] using
      (parameterizedSoninPolarFrame_adjoint_comp_self lambda 1 S (by norm_num))
  have htransport :=
    suffixEulerAmbientProduct_comp_emptyPolarFrame lambda S
  have hadjoint := congrArg ContinuousLinearMap.adjoint htransport
  have hleft : ContinuousLinearMap.adjoint terminal ∘L
      ContinuousLinearMap.adjoint ambient ∘L finalFrame =
      ContinuousLinearMap.adjoint transition := by
    have hadjoint' := hadjoint
    simp only [ContinuousLinearMap.adjoint_comp] at hadjoint'
    have hcompose := congrArg
      (fun T : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
        T ∘L finalFrame) hadjoint'
    simp only [ContinuousLinearMap.comp_assoc] at hcompose
    rw [hfinal, ContinuousLinearMap.comp_id] at hcompose
    exact hcompose
  have htelescope :=
    suffixEulerAmbientProduct_adjoint_comp_terminalPolarFrame lambda S
  apply ContinuousLinearMap.ext
  intro x
  have hleftPoint := DFunLike.congr_fun hleft x
  have htelPoint := DFunLike.congr_fun htelescope x
  have hterminalPoint := DFunLike.congr_fun hterminal
    (ContinuousLinearMap.adjoint transition x)
  have happly := congrArg
    (fun z : finiteSCarrier => ContinuousLinearMap.adjoint terminal z)
    htelPoint
  change (ContinuousLinearMap.adjoint terminal)
      ((ContinuousLinearMap.adjoint ambient) (finalFrame x)) =
    (ContinuousLinearMap.adjoint terminal)
      (terminal ((ContinuousLinearMap.adjoint transition) x) +
        (suffixEulerBoundaryOutputMaps lambda S).sum x) at happly
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply] at hleftPoint htelPoint hterminalPoint

  rw [map_add, hleftPoint, hterminalPoint] at happly
  have hcancel : ContinuousLinearMap.adjoint transition x + 0 =
      ContinuousLinearMap.adjoint transition x +
        ContinuousLinearMap.adjoint terminal
          ((suffixEulerBoundaryOutputMaps lambda S).sum x) := by
    simpa using happly.symm
  exact (add_left_cancel hcancel).symm

theorem suffixEulerTerminalFrame_adjoint_comp_g8MetricVisibleBoundaryCoframe_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    ContinuousLinearMap.adjoint (newSuffixFrame lambda []) ∘L
        g8MetricVisibleBoundaryCoframe lambda family = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  let sqrt := parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
    (by norm_num)
  have horth := DFunLike.congr_fun
    (suffixEulerTerminalFrame_adjoint_comp_boundarySum_eq_zero
      lambda family.visiblePrimes) (sqrt x)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply] at horth
  simp only [g8MetricVisibleBoundaryCoframe,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    map_smul]
  rw [finiteEulerMetricCoframeBoundaryMaps, sum_map_comp_apply]
  change (finiteEulerUpperFactor family.visiblePrimes : ℂ) •
      (ContinuousLinearMap.adjoint (newSuffixFrame lambda [])
        ((suffixEulerBoundaryOutputMaps lambda family.visiblePrimes).sum
          (sqrt x))) = 0
  rw [horth]
  simp

end
end C1G8P1BoundaryOrthogonality
end Source
end ConnesWeilRH
