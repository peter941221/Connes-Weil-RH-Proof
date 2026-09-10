import ConnesWeilRH.Dev.C1G8P1BoundaryChannelLedger

/-!
# G8 P1 aggregate boundary trace ledger

The survivor--boundary channel is a finite sum over the visible-prime
boundary maps.  This leaf lifts that operator identity to the ordinary trace
on the same source basis.  It deliberately stops before identifying an
individual boundary map with a radial prime-power crossing.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1BoundaryTraceLedger

open CCM25Concrete
open CC20Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSGramResponse
open CCM25Concrete.CCM24FiniteSParameterizedEulerProduct
open CCM25Concrete.CCM24FiniteSTransportBounds
open CCM25Concrete.CCM24FiniteSSchurPolarTelescoping
open C1G8P1MetricChannels
open C1G8P1BoundaryChannelLedger
open C1G8AdjointShearGram
open CC20Concrete.PositiveTrace
open scoped InnerProduct InnerProductSpace Topology

noncomputable section

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

theorem ordinaryTraceAlong_g8MetricCutoffSurvivorVisibleBoundary_eq_upperFactor_sum
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    ordinaryTraceAlong sourceBasis
        (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
          (g8MetricSurvivorCoframe lambda family)
          (g8MetricVisibleBoundaryCoframe lambda family)) =
      (finiteEulerUpperFactor family.visiblePrimes : ℂ) *
        (List.map (fun boundary =>
          ordinaryTraceAlong sourceBasis
            (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
              (g8MetricSurvivorCoframe lambda family) boundary))
          (finiteEulerMetricCoframeBoundaryMaps lambda family)).sum := by
  let channel := fun boundary :
      sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
    g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n
      (g8MetricSurvivorCoframe lambda family) boundary
  have hchannel : ∀ boundary,
      IsTraceClassAlong sourceBasis (channel boundary) := by
    intro boundary
    exact g8MetricCutoffChannel_isTraceClassAlong owner lambda family
      globalBasis sourceBasis n (g8MetricSurvivorCoframe lambda family) boundary
  have hclass : ∀ maps : List (sourceSoninCarrier lambda →L[ℂ] finiteSCarrier),
      IsTraceClassAlong sourceBasis (List.map channel maps).sum := by
    intro maps
    induction maps with
    | nil =>
        simpa using (isTraceClassAlong_zero sourceBasis)
    | cons boundary maps ih =>
        simp only [List.map_cons, List.sum_cons]
        apply isTraceClassAlong_add
        · exact hchannel boundary
        · exact ih
  have htraceSum : ∀ maps : List (sourceSoninCarrier lambda →L[ℂ] finiteSCarrier),
      ordinaryTraceAlong sourceBasis (List.map channel maps).sum =
        (List.map (fun boundary => ordinaryTraceAlong sourceBasis (channel boundary)) maps).sum := by
    intro maps
    induction maps with
    | nil =>
        simp [ordinaryTraceAlong]
    | cons boundary maps ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ordinaryTraceAlong_add sourceBasis]
        · rw [ih]
        · exact hchannel boundary
        · exact hclass maps
  rw [g8MetricCutoffSurvivorVisibleBoundary_eq_boundarySum]
  rw [ordinaryTraceAlong_smul sourceBasis]
  · rw [htraceSum (finiteEulerMetricCoframeBoundaryMaps lambda family)]
  · exact hclass (finiteEulerMetricCoframeBoundaryMaps lambda family)

end
end C1G8P1BoundaryTraceLedger
end Source
end ConnesWeilRH
