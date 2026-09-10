import ConnesWeilRH.Dev.C1G8P1BoundaryOrthogonality

/-!
# G8 P1 survivor--boundary coframe Pythagorean identity

The Schur telescope makes the terminal survivor orthogonal to the aggregate
boundary coframe.  This leaf records the resulting exact Gram identity for
the literal metric coframe.  It is an energy/Gram identity on the same
`CompactLog` owner; it does not identify the boundary term with a radial
crossing and does not assert a detector-weighted cancellation.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1CoframePythagorean

open CCM25Concrete
open CC20Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSCoframeResponse
open CCM25Concrete.CCM24FiniteSGramResponse
open CCM25Concrete.CCM24FiniteSFixedSourcePolar
open CCM25Concrete.CCM24FiniteSTransportBounds
open CCM25Concrete.CCM24FiniteSActualSchurCascade
open CCM25Concrete.CCM24FiniteSSchurPolarTelescoping
open C1G8P1MetricChannels
open C1G8P1BoundaryOrthogonality
open scoped InnerProduct InnerProductSpace

noncomputable section

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
    (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

theorem g8MetricSurvivor_adjoint_comp_visibleBoundary_eq_zero
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (g8MetricSurvivorCoframe lambda family).adjoint ∘L
        g8MetricVisibleBoundaryCoframe lambda family = 0 := by
  let u := (finiteEulerUpperFactor family.visiblePrimes : ℂ)
  let terminal := newSuffixFrame lambda []
  let transition := suffixEulerTransitionProduct lambda family.visiblePrimes
  let root := parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes
    (by norm_num)
  let boundary := (suffixEulerBoundaryOutputMaps lambda family.visiblePrimes).sum
  have h0 : terminal.adjoint ∘L boundary = 0 := by
    simpa only [terminal, boundary] using
      suffixEulerTerminalFrame_adjoint_comp_boundarySum_eq_zero
        lambda family.visiblePrimes
  have h0' : terminal.adjoint ∘L boundary ∘L root = 0 := by
    rw [← ContinuousLinearMap.comp_assoc, h0]
    simp
  have hbase :
      (terminal ∘L transition.adjoint ∘L root).adjoint ∘L
          (boundary ∘L root) = 0 := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp]
    simp only [ContinuousLinearMap.comp_assoc]
    rw [h0']
    simp
  have hscaled :
      (u • (terminal ∘L transition.adjoint ∘L root)).adjoint ∘L
          (u • (boundary ∘L root)) = 0 := by
    rw [ContinuousLinearMap.adjoint.map_smulₛₗ]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, map_smul]
    have hx := DFunLike.congr_fun hbase x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at hx
    rw [hx]
    simp
  have hsurvivor : g8MetricSurvivorCoframe lambda family =
      u • (terminal ∘L transition.adjoint ∘L root) := by
    rfl
  have hboundary : g8MetricVisibleBoundaryCoframe lambda family =
      u • (boundary ∘L root) := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [g8MetricVisibleBoundaryCoframe,
      finiteEulerMetricCoframeBoundaryMaps, List.map_map, Function.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      sum_map_comp_apply, u, boundary, root]
  rw [hsurvivor, hboundary]
  exact hscaled

theorem finiteEulerMetricCoframe_adjoint_comp_eq_survivor_add_boundary
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (finiteEulerMetricCoframe lambda family).adjoint ∘L
        finiteEulerMetricCoframe lambda family =
      (g8MetricSurvivorCoframe lambda family).adjoint ∘L
          g8MetricSurvivorCoframe lambda family +
        (g8MetricVisibleBoundaryCoframe lambda family).adjoint ∘L
          g8MetricVisibleBoundaryCoframe lambda family := by
  let S := g8MetricSurvivorCoframe lambda family
  let B := g8MetricVisibleBoundaryCoframe lambda family
  have hSB : S.adjoint ∘L B = 0 := by
    simpa only [S, B] using
      g8MetricSurvivor_adjoint_comp_visibleBoundary_eq_zero lambda family
  have hBS : B.adjoint ∘L S = 0 := by
    have hadj := congrArg ContinuousLinearMap.adjoint hSB
    have hz : ContinuousLinearMap.adjoint
        (0 : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda) = 0 := by
      apply ContinuousLinearMap.ext
      intro x
      simp
    rw [hz] at hadj
    simpa only [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint] using hadj
  rw [finiteEulerMetricCoframe_eq_g8MetricSurvivor_add_visibleBoundary]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.adjoint.map_add, map_add,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
  have hSBx := DFunLike.congr_fun hSB x
  have hBSx := DFunLike.congr_fun hBS x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at hSBx hBSx
  rw [hSBx, hBSx]
  abel

end
end C1G8P1CoframePythagorean
end Source
end ConnesWeilRH
