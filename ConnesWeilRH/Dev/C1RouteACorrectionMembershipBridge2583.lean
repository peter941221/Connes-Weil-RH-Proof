import ConnesWeilRH.Dev.C1RouteAAnalyticMomentSystem
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.CC20YoshidaConvolution.CompactLogTest

namespace ConnesWeilRH.Dev

noncomputable def actualCorrectionOwner2351 (modulations : Fin 30 → ℝ) (nodes target : Fin 30 → ℂ) :
    Fin 30 → ℂ :=
  ownerMomentSolution2351 modulations nodes target

theorem actualCorrectionOwner2351_realizes
    (modulations : Fin 30 → ℝ) (nodes target : Fin 30 → ℂ)
    (hdet : IsUnit (ownerMomentMatrix2351 modulations nodes).det)
    (row : Fin 30) :
    laplaceAt (correctedPhysicalCompactLogTest
      (actualCorrectionOwner2351 modulations nodes target) modulations) (nodes row) =
      target row := by
  exact ownerMomentSolution2351_realizes modulations nodes target hdet row

theorem correctionCoefficientBox_mem_of_component_distance2583
    (i : Fin 30) (coefficient : ℂ)
    (hre : |coefficient.re - (correctionCoefficientCenter2570 i).re| ≤
      ((correctionCoefficientBox2570 i).reHi -
        (correctionCoefficientBox2570 i).reLo) / 2)
    (him : |coefficient.im - (correctionCoefficientCenter2570 i).im| ≤
      ((correctionCoefficientBox2570 i).imHi -
        (correctionCoefficientBox2570 i).imLo) / 2) :
    (correctionCoefficientBox2570 i).Mem coefficient := by
  change (correctionCoefficientBox2570 i).reLo ≤ coefficient.re ∧
    coefficient.re ≤ (correctionCoefficientBox2570 i).reHi ∧
    (correctionCoefficientBox2570 i).imLo ≤ coefficient.im ∧
    coefficient.im ≤ (correctionCoefficientBox2570 i).imHi
  have hcenter_re :
      (correctionCoefficientCenter2570 i).re =
        ((correctionCoefficientBox2570 i).reLo +
          (correctionCoefficientBox2570 i).reHi) / 2 := rfl
  have hcenter_im :
      (correctionCoefficientCenter2570 i).im =
        ((correctionCoefficientBox2570 i).imLo +
          (correctionCoefficientBox2570 i).imHi) / 2 := rfl
  rw [hcenter_re] at hre
  rw [hcenter_im] at him
  rcases abs_le.mp hre with ⟨hre_lo, hre_hi⟩
  rcases abs_le.mp him with ⟨him_lo, him_hi⟩
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

theorem actualCorrectionOwner2351_mem_of_component_distances2583
    (modulations : Fin 30 → ℝ) (nodes target : Fin 30 → ℂ)
    (hcomponent : ∀ i : Fin 30,
      |(actualCorrectionOwner2351 modulations nodes target i).re -
          (correctionCoefficientCenter2570 i).re| ≤
        ((correctionCoefficientBox2570 i).reHi -
          (correctionCoefficientBox2570 i).reLo) / 2 ∧
      |(actualCorrectionOwner2351 modulations nodes target i).im -
          (correctionCoefficientCenter2570 i).im| ≤
        ((correctionCoefficientBox2570 i).imHi -
          (correctionCoefficientBox2570 i).imLo) / 2) :
    ∀ i : Fin 30,
      (correctionCoefficientBox2570 i).Mem
        (actualCorrectionOwner2351 modulations nodes target i) := by
  intro i
  exact correctionCoefficientBox_mem_of_component_distance2583 i
    (actualCorrectionOwner2351 modulations nodes target i)
    (hcomponent i).1 (hcomponent i).2

end ConnesWeilRH.Dev
