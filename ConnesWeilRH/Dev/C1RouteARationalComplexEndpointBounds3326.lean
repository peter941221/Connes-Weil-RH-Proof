import ConnesWeilRH.Dev.C1RouteARationalEndpointBounds3325

namespace ConnesWeilRH.Dev

def ratRectEndpointAbsBound3326 (a : RatRect3276) : ℚ :=
  max (max |a.reLo| |a.reHi|) (max |a.imLo| |a.imHi|)

theorem ratRectEndpointAbsBound3326_nonneg (a : RatRect3276) :
    0 ≤ ratRectEndpointAbsBound3326 a := by
  unfold ratRectEndpointAbsBound3326
  exact le_trans
    (le_trans (abs_nonneg _) (le_max_right _ _))
    (le_max_right _ _)

set_option maxHeartbeats 10000000 in
theorem ratRect_mul_reHi_le_abs_bound3326
    (a b : RatRect3276) :
    (RatRect3276.mul a b).reHi ≤
      2 * ratRectEndpointAbsBound3326 a *
        ratRectEndpointAbsBound3326 b := by
  let ar : RatInterval3276 := ⟨a.reLo, a.reHi⟩
  let ai : RatInterval3276 := ⟨a.imLo, a.imHi⟩
  let br : RatInterval3276 := ⟨b.reLo, b.reHi⟩
  let bi : RatInterval3276 := ⟨b.imLo, b.imHi⟩
  have har : ratIntervalEndpointAbsBound3325 ar ≤
      ratRectEndpointAbsBound3326 a := by
    change max |a.reLo| |a.reHi| ≤
      max (max |a.reLo| |a.reHi|) (max |a.imLo| |a.imHi|)
    exact le_max_left _ _
  have hai : ratIntervalEndpointAbsBound3325 ai ≤
      ratRectEndpointAbsBound3326 a := by
    change max |a.imLo| |a.imHi| ≤
      max (max |a.reLo| |a.reHi|) (max |a.imLo| |a.imHi|)
    exact le_max_right _ _
  have hbr : ratIntervalEndpointAbsBound3325 br ≤
      ratRectEndpointAbsBound3326 b := by
    change max |b.reLo| |b.reHi| ≤
      max (max |b.reLo| |b.reHi|) (max |b.imLo| |b.imHi|)
    exact le_max_left _ _
  have hbi : ratIntervalEndpointAbsBound3325 bi ≤
      ratRectEndpointAbsBound3326 b := by
    change max |b.imLo| |b.imHi| ≤
      max (max |b.reLo| |b.reHi|) (max |b.imLo| |b.imHi|)
    exact le_max_right _ _
  have hrr := ratInterval_mul_hi_le_abs_bound3325 ar br
  have hii := ratInterval_mul_lo_ge_neg_abs_bound3325 ai bi
  have hrr' : (RatInterval3276.mul ar br).hi ≤
      ratRectEndpointAbsBound3326 a * ratRectEndpointAbsBound3326 b := by
    exact le_trans hrr (mul_le_mul har hbr
      (ratIntervalEndpointAbsBound3325_nonneg br)
      (ratRectEndpointAbsBound3326_nonneg a))
  have hii' : -(ratRectEndpointAbsBound3326 a *
      ratRectEndpointAbsBound3326 b) ≤ (RatInterval3276.mul ai bi).lo := by
    exact le_trans
      (neg_le_neg (mul_le_mul hai hbi
        (ratIntervalEndpointAbsBound3325_nonneg bi)
        (ratRectEndpointAbsBound3326_nonneg a))) hii
  change (RatInterval3276.mul ar br).hi -
      (RatInterval3276.mul ai bi).lo ≤ _
  linarith

end ConnesWeilRH.Dev
