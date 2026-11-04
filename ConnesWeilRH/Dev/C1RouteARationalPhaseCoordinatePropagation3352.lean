import ConnesWeilRH.Dev.C1RouteARationalPhaseCoordinateBounds3351
import ConnesWeilRH.Dev.C1RouteARationalTaylorEndpoint3344

namespace ConnesWeilRH.Dev

def ratRectRealEndpointAbsBound3352 (a : RatRect3276) : ℚ :=
  max |a.reLo| |a.reHi|

def ratRectImagEndpointAbsBound3352 (a : RatRect3276) : ℚ :=
  max |a.imLo| |a.imHi|

theorem ratInterval_mul_endpoint_abs_le3352
    (x y : RatInterval3276) (X Y : ℚ)
    (hx : ratIntervalEndpointAbsBound3325 x ≤ X)
    (hy : ratIntervalEndpointAbsBound3325 y ≤ Y)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    |(RatInterval3276.mul x y).lo| ≤ X * Y ∧
    |(RatInterval3276.mul x y).hi| ≤ X * Y := by
  have hhi := ratInterval_mul_hi_le_abs_bound3325 x y
  have hlo := ratInterval_mul_lo_ge_neg_abs_bound3325 x y
  have hhi' : (RatInterval3276.mul x y).hi ≤ X * Y := by
    exact le_trans hhi (mul_le_mul hx hy
      (ratIntervalEndpointAbsBound3325_nonneg y) hX)
  have hlo' : -(X * Y) ≤ (RatInterval3276.mul x y).lo := by
    exact le_trans
      (neg_le_neg (mul_le_mul hx hy
        (ratIntervalEndpointAbsBound3325_nonneg y) hX)) hlo
  have horder := ratInterval_mul_order3344 x y
  constructor
  · exact (abs_le).mpr ⟨hlo', le_trans horder hhi'⟩
  · exact (abs_le).mpr ⟨le_trans hlo' horder, hhi'⟩

theorem ratRect_mul_square_re_abs_le3352
    (a : RatRect3276) (R I : ℚ)
    (hre : ratRectRealEndpointAbsBound3352 a ≤ R)
    (him : ratRectImagEndpointAbsBound3352 a ≤ I)
    (hR : 0 ≤ R) (hI : 0 ≤ I) :
    ratRectRealEndpointAbsBound3352 (RatRect3276.mul a a) ≤
      R * R + I * I := by
  let ar : RatInterval3276 := ⟨a.reLo, a.reHi⟩
  let ai : RatInterval3276 := ⟨a.imLo, a.imHi⟩
  have har : ratIntervalEndpointAbsBound3325 ar ≤ R := by
    exact hre
  have hai : ratIntervalEndpointAbsBound3325 ai ≤ I := by
    exact him
  have hrr := ratInterval_mul_endpoint_abs_le3352 ar ar R R har har hR hR
  have hii := ratInterval_mul_endpoint_abs_le3352 ai ai I I hai hai hI hI
  have hRR : 0 ≤ R * R := mul_nonneg hR hR
  have hII : 0 ≤ I * I := mul_nonneg hI hI
  unfold ratRectRealEndpointAbsBound3352 RatRect3276.mul
  dsimp [ar, ai] at hrr hii
  apply max_le
  · calc
      |(RatInterval3276.mul ar ar).lo -
          (RatInterval3276.mul ai ai).hi| ≤
          |(RatInterval3276.mul ar ar).lo| +
            |(RatInterval3276.mul ai ai).hi| := by
              calc
                |(RatInterval3276.mul ar ar).lo -
                    (RatInterval3276.mul ai ai).hi| =
                    |(RatInterval3276.mul ar ar).lo +
                      -(RatInterval3276.mul ai ai).hi| := by
                        congr 1 <;> ring
                _ ≤ |(RatInterval3276.mul ar ar).lo| +
                    |-(RatInterval3276.mul ai ai).hi| := abs_add_le _ _
                _ = |(RatInterval3276.mul ar ar).lo| +
                    |(RatInterval3276.mul ai ai).hi| := by rw [abs_neg]
      _ ≤ R * R + I * I := add_le_add hrr.1 hii.2
  · calc
      |(RatInterval3276.mul ar ar).hi -
          (RatInterval3276.mul ai ai).lo| ≤
          |(RatInterval3276.mul ar ar).hi| +
            |(RatInterval3276.mul ai ai).lo| := by
              calc
                |(RatInterval3276.mul ar ar).hi -
                    (RatInterval3276.mul ai ai).lo| =
                    |(RatInterval3276.mul ar ar).hi +
                      -(RatInterval3276.mul ai ai).lo| := by
                        congr 1 <;> ring
                _ ≤ |(RatInterval3276.mul ar ar).hi| +
                    |-(RatInterval3276.mul ai ai).lo| := abs_add_le _ _
                _ = |(RatInterval3276.mul ar ar).hi| +
                    |(RatInterval3276.mul ai ai).lo| := by rw [abs_neg]
      _ ≤ R * R + I * I := add_le_add hrr.2 hii.1

theorem ratRect_mul_square_im_abs_le3352
    (a : RatRect3276) (R I : ℚ)
    (hre : ratRectRealEndpointAbsBound3352 a ≤ R)
    (him : ratRectImagEndpointAbsBound3352 a ≤ I)
    (hR : 0 ≤ R) (hI : 0 ≤ I) :
    ratRectImagEndpointAbsBound3352 (RatRect3276.mul a a) ≤
      2 * R * I := by
  let ar : RatInterval3276 := ⟨a.reLo, a.reHi⟩
  let ai : RatInterval3276 := ⟨a.imLo, a.imHi⟩
  have har : ratIntervalEndpointAbsBound3325 ar ≤ R := hre
  have hai : ratIntervalEndpointAbsBound3325 ai ≤ I := him
  have hri := ratInterval_mul_endpoint_abs_le3352 ar ai R I har hai hR hI
  have hir := ratInterval_mul_endpoint_abs_le3352 ai ar I R hai har hI hR
  have hRI : 0 ≤ R * I := mul_nonneg hR hI
  unfold ratRectImagEndpointAbsBound3352 RatRect3276.mul
  dsimp [ar, ai] at hri hir
  apply max_le
  · exact (abs_add_le _ _).trans (by
      calc
        |(RatInterval3276.mul ar ai).lo| +
            |(RatInterval3276.mul ai ar).lo| ≤
            R * I + I * R := add_le_add hri.1 hir.1
        _ = 2 * R * I := by ring)
  · exact (abs_add_le _ _).trans (by
      calc
        |(RatInterval3276.mul ar ai).hi| +
            |(RatInterval3276.mul ai ar).hi| ≤
            R * I + I * R := add_le_add hri.2 hir.2
        _ = 2 * R * I := by ring)

theorem ratPhaseRect_square_coordinate_bounds3352_cell0_family4 :
    ratRectRealEndpointAbsBound3352
        (RatRect3276.mul
          (ratPhaseRect3279
            (record2680PhaseAngleRat3279 0 4))
          (ratPhaseRect3279
            (record2680PhaseAngleRat3279 0 4))) ≤
      (1 : ℚ) * 1 + (1 / 2 : ℚ) * (1 / 2) ∧
    ratRectImagEndpointAbsBound3352
        (RatRect3276.mul
          (ratPhaseRect3279
            (record2680PhaseAngleRat3279 0 4))
          (ratPhaseRect3279
            (record2680PhaseAngleRat3279 0 4))) ≤
      2 * 1 * (1 / 2 : ℚ) := by
  constructor
  · apply ratRect_mul_square_re_abs_le3352
    · exact ratPhaseRealEndpointAbsBound3351_cell0_family4
    · exact ratPhaseImagEndpointAbsBound3351_cell0_family4
    · norm_num
    · norm_num
  · apply ratRect_mul_square_im_abs_le3352
    · exact ratPhaseRealEndpointAbsBound3351_cell0_family4
    · exact ratPhaseImagEndpointAbsBound3351_cell0_family4
    · norm_num
    · norm_num

end ConnesWeilRH.Dev
