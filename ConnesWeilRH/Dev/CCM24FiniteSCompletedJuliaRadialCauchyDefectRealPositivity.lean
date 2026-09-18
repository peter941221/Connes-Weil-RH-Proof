import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundaryCauchyPairProducer

/-!
# Real positivity of the radial Cauchy defect

The radial boundary crossing is the positive Cauchy square `C† C`.  The
source modules already provide its exact named-basis trace readback as the
sum of squared crossing columns.  This leaf exports the scalar consequence
needed by a detector-specific positive aggregate: the real part of that
ordinary trace is nonnegative.

This is a genuine positive channel, not a substitute for the missing signed
boundary factorization.  The latter is still required to identify the whole
finite-Euler owner with this channel.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRadialCauchyDefectRealPositivity

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open AntiresonantFrameLossRadialBoundarySplit
open AntiresonantFrameLossRadialBoundaryCauchyEnergy
open AntiresonantFrameLossRadialBoundaryCauchyDefect
open CCM24FiniteSProjectionTrace

theorem radialSoninBoundaryCauchyDefect_trace_re_nonnegative
    {ι : Type*} (sourceBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hcross : Summable fun i =>
      ‖radialSoninBoundaryCrossing p S (sourceBasis i)‖ ^ 2) :
    0 ≤ (ordinaryTraceAlong sourceBasis
      (radialSoninBoundaryCauchyDefect p S)).re := by
  rw [radialSoninBoundaryCauchyDefect_ordinaryTrace_eq_crossingEnergy
    sourceBasis p S hcross]
  simp only [Complex.ofReal_re]
  exact tsum_nonneg (fun i => sq_nonneg _)

end CCM24FiniteSCompletedJuliaRadialCauchyDefectRealPositivity
end CCM25Concrete
end Source
end ConnesWeilRH
