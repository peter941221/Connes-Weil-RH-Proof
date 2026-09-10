import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundaryColumnBridge

/-!
# G8 P1 canonical radial-boundary bound

The source-side radial column factorization already has a canonical choice:
the first retained radial coordinate, scaled by the inverse Euler coefficient.
This leaf specializes the generic column estimate to that actual choice.  It
is a quantitative transport input for the future same-owner comparison; it
does not identify a metric coframe boundary map with a prime-power trace.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1CanonicalRadialBoundaryBound

open CCM25Concrete
open CC20Concrete
open CCM25Concrete.AntiresonantFrameLossRadialBoundaryColumnBridge
open CCM25Concrete.AntiresonantFrameLossRadialBoundarySplit
open CCM25Concrete.AntiresonantFrameLossCommutator
open CCM25Concrete.CCM24FiniteSActualSchurCascade
open CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM25Concrete.CCM24FiniteSFrameGramCalculus
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24UnitScaleProlateAlignment
open scoped InnerProduct InnerProductSpace

noncomputable section

theorem norm_radialSoninBoundaryCrossing_comp_newSuffixFrame_apply_le_canonical
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier unitSoninScale) :
    ‖radialSoninBoundaryCrossing p S
        (newSuffixFrame unitSoninScale S x)‖ ≤
      (32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) *
        ‖newFrameAntiresonantColumn unitSoninScale p S x‖ := by
  exact norm_radialSoninBoundaryCrossing_comp_newSuffixFrame_apply_le_of_data
    (canonicalRadialBoundarySourceColumnFactorizationData p S) x

theorem normSq_radialSoninBoundaryCrossing_comp_newSuffixFrame_apply_le_canonical
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier unitSoninScale) :
    ‖radialSoninBoundaryCrossing p S
        (newSuffixFrame unitSoninScale S x)‖ ^ 2 ≤
      (32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) ^ 2 *
        ‖newFrameAntiresonantColumn unitSoninScale p S x‖ ^ 2 := by
  exact normSq_radialSoninBoundaryCrossing_comp_newSuffixFrame_apply_le_of_data
    (canonicalRadialBoundarySourceColumnFactorizationData p S) x

end
end C1G8P1CanonicalRadialBoundaryBound
end Source
end ConnesWeilRH
