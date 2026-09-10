import ConnesWeilRH.Dev.C1G8P1MetricChannels

/-!
# G8 P1 metric cutoff positive trace

This leaf packages the already-proved fixed-cutoff positivity and trace-class
owner into the scalar inequality needed by a later endpoint comparison.  It
does not identify the scalar with a prime sum or a limit.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1MetricPositiveTrace

open CCM25Concrete
open CC20Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSGramResponse
open C1G8P1MetricBoundary
open C1G8P1MetricChannels
open CC20Concrete.PositiveTrace
open scoped InnerProduct InnerProductSpace Topology

noncomputable section

theorem g8PhysicalMetricCutoffOperator_trace_re_nonnegative
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat) :
    0 ≤ (ordinaryTraceAlong sourceBasis
      (g8PhysicalMetricCutoffOperator owner lambda family globalBasis sourceBasis n)).re := by
  let T := g8PhysicalMetricCutoffOperator owner lambda family globalBasis sourceBasis n
  have hpositive : T.IsPositive := by
    simpa only [T] using
      (g8PhysicalMetricCutoffOperator_isPositive owner lambda family globalBasis sourceBasis n)
  have htrace : IsTraceClassAlong sourceBasis T := by
    simpa only [T] using
      (g8PhysicalMetricCutoffOperator_isTraceClassAlong owner lambda family
        globalBasis sourceBasis n)
  change 0 ≤ (ordinaryTraceAlong sourceBasis T).re
  rw [ordinaryTraceAlong]
  rw [Complex.re_tsum htrace]
  exact tsum_nonneg (fun i => hpositive.re_inner_nonneg_right (sourceBasis i))

end
end C1G8P1MetricPositiveTrace
end Source
end ConnesWeilRH
