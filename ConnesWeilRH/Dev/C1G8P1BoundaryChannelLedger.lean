import ConnesWeilRH.Dev.C1G8P1MetricChannels

/-!
# G8 P1 survivor--boundary channel ledger

This leaf expands the two linear survivor/boundary channels through the
ordered visible-prime boundary list.  It is only an operator identity on the
same literal cutoff and selected detector; no finite-prime scalar readback or
endpoint limit is asserted.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1BoundaryChannelLedger

open CCM25Concrete
open CC20Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSGramResponse
open CCM25Concrete.CCM24FiniteSParameterizedEulerProduct
open CCM25Concrete.CCM24FiniteSTransportBounds
open CCM25Concrete.CCM24FiniteSSchurPolarTelescoping
open C1G8P1MetricChannels
open C1G8AdjointShearGram
open CC20Concrete.PositiveTrace
open scoped InnerProduct InnerProductSpace Topology

noncomputable section

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

theorem comp_sum_eq_sum_comp
    {H K L : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    [NormedAddCommGroup L] [NormedSpace ℂ L]
    (left : K →L[ℂ] L) (maps : List (H →L[ℂ] K))
    (right : H →L[ℂ] H) :
    left ∘L maps.sum ∘L right =
      (maps.map (fun middle => left ∘L middle ∘L right)).sum := by
  induction maps with
  | nil =>
      apply ContinuousLinearMap.ext
      intro x
      simp
  | cons middle maps ih =>
      apply ContinuousLinearMap.ext
      intro x
      simp only [List.sum_cons, List.map_cons,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
      rw [← ih]
      simp only [map_add]
      simp only [ContinuousLinearMap.comp_apply]

theorem comp_smul_sum_eq_smul_sum_comp
    {H K L : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    [NormedAddCommGroup L] [NormedSpace ℂ L]
    (left : K →L[ℂ] L) (u : ℂ) (maps : List (H →L[ℂ] K))
    (right : H →L[ℂ] H) :
    left ∘L (u • maps.sum) ∘L right =
      u • (maps.map (fun middle => left ∘L middle ∘L right)).sum := by
  apply ContinuousLinearMap.ext
  intro x
  have h := congrArg (fun T => T x) (comp_sum_eq_sum_comp left maps right)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    map_smul] at h ⊢
  rw [h]

theorem g8MetricCutoffSurvivorVisibleBoundary_eq_boundarySum
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
        (g8MetricSurvivorCoframe lambda family)
        (g8MetricVisibleBoundaryCoframe lambda family) =
      (finiteEulerUpperFactor family.visiblePrimes : ℂ) •
      (List.map (fun boundary =>
            g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
              (g8MetricSurvivorCoframe lambda family) boundary)
        (finiteEulerMetricCoframeBoundaryMaps lambda family)).sum := by
  let C := (sourceInclusion lambda)† ∘L
    (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left
  let A := C† ∘L (g8MetricSurvivorCoframe lambda family)† ∘L
    detectorOperator owner
  change A ∘L
      ((finiteEulerUpperFactor family.visiblePrimes : ℂ) •
        (finiteEulerMetricCoframeBoundaryMaps lambda family).sum) ∘L C =
    (finiteEulerUpperFactor family.visiblePrimes : ℂ) •
      (List.map (fun boundary => A ∘L boundary ∘L C)
        (finiteEulerMetricCoframeBoundaryMaps lambda family)).sum
  exact comp_smul_sum_eq_smul_sum_comp A
    (finiteEulerUpperFactor family.visiblePrimes : ℂ)
    (finiteEulerMetricCoframeBoundaryMaps lambda family) C

end
end C1G8P1BoundaryChannelLedger
end Source
end ConnesWeilRH
