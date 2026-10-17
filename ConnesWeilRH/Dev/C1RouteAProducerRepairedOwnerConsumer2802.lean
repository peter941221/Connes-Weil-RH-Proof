import ConnesWeilRH.Dev.C1RouteAProducerWired
import ConnesWeilRH.Dev.C1RepairedOwnerTotalKnownError2801

namespace ConnesWeilRH
namespace Dev

open ConnesWeilRH.Source.C1RouteAItem5Arithmetic
open ConnesWeilRH.Source.CC20YoshidaConvolution.CompactLogTest
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.C1SpectralWeil
open ConnesWeilRH.Source.CC20YoshidaNearZeros

/-- Producer consumer with the repaired-owner charge interface. The only
remaining owner-specific input is `chargeRest <= record2686RepairedOwnerTotal2800`.
This theorem does not identify the selected detector with that owner. -/
theorem a005_item5_producer_wired_repaired_owner_charge2802
    (b c : CompactLogTest)
    (henvelope : ∀ sigma ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2),
      min (stripSecondNorm sigma (b.test : ℝ → ℂ) *
            stripNorm sigma (c.test : ℝ → ℂ))
          (stripSecondNorm sigma (c.test : ℝ → ℂ) *
            stripNorm sigma (b.test : ℝ → ℂ))
        ≤ stripGridMax2303 * stripTransfer2303)
    {qLo gap chargeRest windowCharge tailCharge : Real}
    (hmargin : margin2249 ≤ -qLo)
    (hownerCharge : chargeRest ≤ record2686RepairedOwnerTotal2800)
    (hsplit : gap ≤ windowCharge + tailCharge)
    (hwindow : windowCharge ≤ windowCharge2309)
    (htail : tailCharge ≤ tailCharge2307) :
    (∑' n : Nat, ∑' rho : spectralHeightShell (n + 1),
        spectralNormTerm (b.convolution c) rho.1) +
      chargeRest + gap + eps0FullTail2249 < -qLo := by
  exact a005_item5_producer_wired_certified_multiplicity_gap_split_envelope
    b c henvelope hmargin
    (chargeRest_le_knownError_of_record2686_total_le2801 hownerCharge)
    hsplit hwindow htail

end Dev
end ConnesWeilRH
