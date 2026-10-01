import ConnesWeilRH.Dev.C1RouteASelectedOwnerFourierInterface
import ConnesWeilRH.Dev.C1RouteAOwnerTest

namespace ConnesWeilRH.Source.C1RouteASelectedOwnerSupport

open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open CC20YoshidaConvolution.CompactLogTest
open ConnesWeilRH.Dev
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open C1RouteAItem5Arithmetic

noncomputable section

theorem selectedOwner_source_support_composed
    (base correction : CompactLogTest) (n : Nat)
    {baseRadius correctionRadius : Real}
    (hbase : Function.support base.test ⊆ Set.Ioo (-baseRadius) baseRadius)
    (hcorrection : Function.support correction.test ⊆
      Set.Ioo (-correctionRadius) correctionRadius) :
    Function.support (selectedOwner base correction n).sourceTest.test ⊆
      Set.Ioo (-((n + 1 : Nat) * baseRadius + correctionRadius))
        ((n + 1 : Nat) * baseRadius + correctionRadius) := by
  rw [selectedOwner_sourceTest]
  apply halfDensityShift_support_subset
  have hiterate := convolutionIterate_support_subset_Ioo base hbase n
  have hcomposed := convolution_support_subset_add_Ioo
    (convolutionIterate base n) correction hiterate hcorrection
  (convert hcomposed using 1; ring_nf)

theorem selectedOwner_square_support_composed
    (base correction : CompactLogTest) (n : Nat)
    {baseRadius correctionRadius : Real}
    (hbase : Function.support base.test ⊆ Set.Ioo (-baseRadius) baseRadius)
    (hcorrection : Function.support correction.test ⊆
      Set.Ioo (-correctionRadius) correctionRadius) :
    Function.support (selectedOwner base correction n).convolutionSquare.test ⊆
      Set.Ioo (-(2 * ((n + 1 : Nat) * baseRadius + correctionRadius)))
        (2 * ((n + 1 : Nat) * baseRadius + correctionRadius)) := by
  have hsource := selectedOwner_source_support_composed base correction n hbase hcorrection
  have hhalf : Function.support (selectedOwner base correction n).sourceTest.test ⊆
      Set.Ioo (-(2 * ((n + 1 : Nat) * baseRadius + correctionRadius)) / 2)
        ((2 * ((n + 1 : Nat) * baseRadius + correctionRadius)) / 2) := by
    (convert hsource using 1; ring_nf)
  exact convolutionSquare_support_subset_symmetric
    (selectedOwner base correction n).sourceTest hhalf

theorem capturedFactor_support_open_pin
    (coefficients : Fin 30 → Complex) (modulations : Fin 30 → Real) :
    Function.support (correctedPhysicalCompactLogTest coefficients modulations).test ⊆
      Set.Ioo (-stripRadius2303) stripRadius2303 := by
  have hstrict : storedWidth 4 ^ 2 < stripRadius2303 := by
    change (1441151880758559 / 562949953421312 : Real) ^ 2 < (6.5536001 : Real)
    norm_num
  intro position hposition
  have hraw : position ∈ Function.support (correctedPhysical coefficients modulations) := by
    simpa only [correctedPhysicalCompactLogTest_toFun] using hposition
  have hclosed := correctedPhysical_tsupport_subset_four coefficients modulations
    (subset_tsupport _ hraw)
  exact ⟨lt_of_lt_of_le (neg_lt_neg hstrict) hclosed.1,
    lt_of_le_of_lt hclosed.2 hstrict⟩

theorem capturedSelectedOwner_square_support_pin
    (baseCoefficients correctionCoefficients : Fin 30 → Complex)
    (modulations : Fin 30 → Real) (n : Nat) :
    Function.support
        (selectedOwner (correctedPhysicalCompactLogTest baseCoefficients modulations)
          (correctedPhysicalCompactLogTest correctionCoefficients modulations)
          n).convolutionSquare.test ⊆
      Set.Ioo (-(2 * ((n + 1 : Nat) * stripRadius2303 + stripRadius2303)))
        (2 * ((n + 1 : Nat) * stripRadius2303 + stripRadius2303)) := by
  exact selectedOwner_square_support_composed _ _ n
    (capturedFactor_support_open_pin baseCoefficients modulations)
    (capturedFactor_support_open_pin correctionCoefficients modulations)

end
end ConnesWeilRH.Source.C1RouteASelectedOwnerSupport
