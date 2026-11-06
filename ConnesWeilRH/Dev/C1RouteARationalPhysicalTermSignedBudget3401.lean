import ConnesWeilRH.Dev.C1RouteARationalWeightedJetSignedSum3399
import ConnesWeilRH.Dev.C1RouteARationalWeightedJetSumEndpoint3386
import ConnesWeilRH.Dev.C1RouteARationalSignedCoordinateBound3342
import ConnesWeilRH.Dev.C1RouteARationalSignedComplex3331

namespace ConnesWeilRH.Dev

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ratCoefficientRect3282_family4_mul_reHi_le_coordinate_budgets3401
    (b : RatRect3276)
    (hre : b.reLo ≤ b.reHi)
    (him : b.imLo ≤ b.imHi)
    (realBudget imagBudget : ℚ)
    (hreal : ratRectRealEndpointAbsBound3342 b ≤ realBudget)
    (himag : ratRectImagEndpointAbsBound3342 b ≤ imagBudget)
    (hrealBudget : realBudget ≤ 7 / 10 ^ 15)
    (himagBudget : imagBudget ≤ 64 / 10 ^ 16 + 1 / 10 ^ 25 + 1 / 10 ^ 33) :
    (RatRect3276.mul (ratCoefficientRect3282 4) b).reHi ≤ 1 := by
  have hcoef : ratCoefficientRect3282 4 =
      ({ reLo := -(6001732121601251 : ℚ) / 32,
         reHi := -(6001732121601251 : ℚ) / 32,
         imLo := -(6739580861423611 : ℚ) / 128,
         imHi := -(6739580861423611 : ℚ) / 128 } : RatRect3276) := by
    norm_num [ratCoefficientRect3282, Matrix.cons_val_four]
  rw [hcoef]
  have hbound := signed_singleton_reHi_le_coordinate_bound3342
    (-(6001732121601251 : ℚ) / 32)
    (-(6739580861423611 : ℚ) / 128) b
    (by norm_num) (by norm_num)
  have hrealMul :
      (6001732121601251 / 32 : ℚ) * ratRectRealEndpointAbsBound3342 b ≤
        (6001732121601251 / 32 : ℚ) * realBudget := by
    exact mul_le_mul_of_nonneg_left hreal (by norm_num)
  have himagMul :
      (6739580861423611 / 128 : ℚ) * ratRectImagEndpointAbsBound3342 b ≤
        (6739580861423611 / 128 : ℚ) * imagBudget := by
    exact mul_le_mul_of_nonneg_left himag (by norm_num)
  have hbound' :
      (RatRect3276.mul (ratCoefficientRect3282 4) b).reHi ≤
        (6001732121601251 / 32 : ℚ) * ratRectRealEndpointAbsBound3342 b +
          (6739580861423611 / 128 : ℚ) * ratRectImagEndpointAbsBound3342 b := by
    rw [hcoef]
    convert hbound using 1 <;> norm_num
  calc
    _ ≤ (6001732121601251 / 32 : ℚ) * realBudget +
        (6739580861423611 / 128 : ℚ) * imagBudget := by
      exact le_trans hbound'
        (add_le_add hrealMul himagMul)
    _ ≤ (6001732121601251 / 32 : ℚ) * (7 / 10 ^ 15) +
        (6739580861423611 / 128 : ℚ) *
          (64 / 10 ^ 16 + 1 / 10 ^ 25 + 1 / 10 ^ 33) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hrealBudget (by norm_num))
        (mul_le_mul_of_nonneg_left himagBudget (by norm_num))
    _ ≤ 1 := by norm_num [div_eq_mul_inv, Rat.cast_def]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem ratWeightedPhysicalTermRect_cell1_order2_family4_reHi_le3401 :
    (ratWeightedPhysicalTermRect3310 2 1 4).reHi ≤ 1 := by
  let jetSum : RatRect3276 :=
    RatRect3276.add
      (RatRect3276.add
        (ratWeightedUnitJetRect3310 2 0 1 4)
        (ratWeightedUnitJetRect3310 2 1 1 4))
      (ratWeightedUnitJetRect3310 2 2 1 4)
  have hordered : jetSum.reLo ≤ jetSum.reHi ∧ jetSum.imLo ≤ jetSum.imHi := by
    simpa [jetSum] using ratWeightedJetSumRect_cell1_order2_family4_ordered3386
  have hrealLo : -(64 / 10 ^ 16 : ℚ) - 1 / 10 ^ 25 - 1 / 10 ^ 33 ≤ jetSum.reLo := by
    simpa [jetSum] using ratWeightedJetSumRect_cell1_order2_family4_reLo_ge3396
  have hrealHi : jetSum.reHi ≤ 7 / 10 ^ 15 := by
    simpa [jetSum] using ratWeightedJetSumRect_cell1_order2_family4_reHi_le3386
  have himagLo :
      -(64 / 10 ^ 16 + 1 / 10 ^ 25 + 1 / 10 ^ 33 : ℚ) ≤ jetSum.imLo := by
    have h := ratWeightedJetSumRect_cell1_order2_family4_imLo_ge3399
    have heq :
        -(64 / 10 ^ 16 + 1 / 10 ^ 25 + 1 / 10 ^ 33 : ℚ) =
          -(64 / 10 ^ 16 : ℚ) - 1 / 10 ^ 25 - 1 / 10 ^ 33 := by ring
    rw [heq]
    simpa [jetSum] using h
  have himagHi : jetSum.imHi ≤
      64 / 10 ^ 16 + 1 / 10 ^ 25 + 1 / 10 ^ 33 := by
    simpa [jetSum] using ratWeightedJetSumRect_cell1_order2_family4_imHi_le3396
  have hreal : ratRectRealEndpointAbsBound3342 jetSum ≤ 7 / 10 ^ 15 := by
    unfold ratRectRealEndpointAbsBound3342
    apply max_le
    · apply (abs_le).2
      constructor
      · linarith [hrealLo]
      · exact hordered.1.trans hrealHi
    · apply (abs_le).2
      constructor
      · linarith [hrealLo, hordered.1]
      · exact hrealHi
  have himag : ratRectImagEndpointAbsBound3342 jetSum ≤
      64 / 10 ^ 16 + 1 / 10 ^ 25 + 1 / 10 ^ 33 := by
    unfold ratRectImagEndpointAbsBound3342
    apply max_le
    · apply (abs_le).2
      constructor
      · exact himagLo
      · exact himagHi
    · apply (abs_le).2
      constructor
      · exact le_trans himagLo hordered.2
      · exact himagHi
  have hmul := ratCoefficientRect3282_family4_mul_reHi_le_coordinate_budgets3401
    jetSum hordered.1 hordered.2
    (7 / 10 ^ 15)
    (64 / 10 ^ 16 + 1 / 10 ^ 25 + 1 / 10 ^ 33)
    hreal himag le_rfl le_rfl
  rw [ratWeightedPhysicalTermRect3310_order2_eq]
  simpa [jetSum] using hmul

end ConnesWeilRH.Dev













