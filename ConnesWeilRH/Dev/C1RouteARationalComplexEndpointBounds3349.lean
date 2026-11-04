import ConnesWeilRH.Dev.C1RouteARationalComplexEndpointBounds3328
import ConnesWeilRH.Dev.C1RouteARationalTaylorEndpoint3344

namespace ConnesWeilRH.Dev

set_option maxHeartbeats 10000000 in
theorem ratRect_mul_endpointAbsBound3349
    (a b : RatRect3276) :
    ratRectEndpointAbsBound3326 (RatRect3276.mul a b) ≤
      2 * ratRectEndpointAbsBound3326 a *
        ratRectEndpointAbsBound3326 b := by
  let A := ratRectEndpointAbsBound3326 a
  let B := ratRectEndpointAbsBound3326 b
  let ar : RatInterval3276 := ⟨a.reLo, a.reHi⟩
  let ai : RatInterval3276 := ⟨a.imLo, a.imHi⟩
  let br : RatInterval3276 := ⟨b.reLo, b.reHi⟩
  let bi : RatInterval3276 := ⟨b.imLo, b.imHi⟩
  have har : ratIntervalEndpointAbsBound3325 ar ≤ A := by
    change max |a.reLo| |a.reHi| ≤
      max (max |a.reLo| |a.reHi|) (max |a.imLo| |a.imHi|)
    exact le_max_left _ _
  have hai : ratIntervalEndpointAbsBound3325 ai ≤ A := by
    change max |a.imLo| |a.imHi| ≤
      max (max |a.reLo| |a.reHi|) (max |a.imLo| |a.imHi|)
    exact le_max_right _ _
  have hbr : ratIntervalEndpointAbsBound3325 br ≤ B := by
    change max |b.reLo| |b.reHi| ≤
      max (max |b.reLo| |b.reHi|) (max |b.imLo| |b.imHi|)
    exact le_max_left _ _
  have hbi : ratIntervalEndpointAbsBound3325 bi ≤ B := by
    change max |b.imLo| |b.imHi| ≤
      max (max |b.reLo| |b.reHi|) (max |b.imLo| |b.imHi|)
    exact le_max_right _ _
  have hA : 0 ≤ A := ratRectEndpointAbsBound3326_nonneg a
  have hB : 0 ≤ B := ratRectEndpointAbsBound3326_nonneg b
  have hpair : ∀ x y : RatInterval3276,
      ratIntervalEndpointAbsBound3325 x ≤ A →
      ratIntervalEndpointAbsBound3325 y ≤ B →
      ∀ q, (RatInterval3276.mul x y).lo ≤ q →
        q ≤ (RatInterval3276.mul x y).hi → |q| ≤ A * B := by
    intro x y hx hy q hqlo hqhi
    have hhi := ratInterval_mul_hi_le_abs_bound3325 x y
    have hlo := ratInterval_mul_lo_ge_neg_abs_bound3325 x y
    have hhi' : (RatInterval3276.mul x y).hi ≤ A * B := by
      exact le_trans hhi (mul_le_mul hx hy
        (ratIntervalEndpointAbsBound3325_nonneg y) hA)
    have hlo' : -(A * B) ≤ (RatInterval3276.mul x y).lo := by
      exact le_trans
        (neg_le_neg (mul_le_mul hx hy
          (ratIntervalEndpointAbsBound3325_nonneg y) hA)) hlo
    exact (abs_le).mpr ⟨le_trans hlo' hqlo, le_trans hqhi hhi'⟩
  have hrrLo := hpair ar br har hbr _ le_rfl
    (ratInterval_mul_order3344 ar br)
  have hrrHi := hpair ar br har hbr _
    (ratInterval_mul_order3344 ar br) le_rfl
  have hiiLo := hpair ai bi hai hbi _ le_rfl
    (ratInterval_mul_order3344 ai bi)
  have hiiHi := hpair ai bi hai hbi _
    (ratInterval_mul_order3344 ai bi) le_rfl
  have hriLo := hpair ar bi har hbi _ le_rfl
    (ratInterval_mul_order3344 ar bi)
  have hriHi := hpair ar bi har hbi _
    (ratInterval_mul_order3344 ar bi) le_rfl
  have hirLo := hpair ai br hai hbr _ le_rfl
    (ratInterval_mul_order3344 ai br)
  have hirHi := hpair ai br hai hbr _
    (ratInterval_mul_order3344 ai br) le_rfl
  have hdouble : A * B + A * B ≤ 2 * A * B := by
    ring_nf
    exact le_rfl
  unfold ratRectEndpointAbsBound3326 RatRect3276.mul
  dsimp [ar, ai, br, bi] at hrrLo hrrHi hiiLo hiiHi hriLo hriHi hirLo hirHi
  apply max_le
  · apply max_le
    · calc
        |(RatInterval3276.mul ar br).lo -
            (RatInterval3276.mul ai bi).hi| ≤
            |(RatInterval3276.mul ar br).lo| +
              |(RatInterval3276.mul ai bi).hi| := by
                calc
                  |(RatInterval3276.mul ar br).lo -
                      (RatInterval3276.mul ai bi).hi| =
                      |(RatInterval3276.mul ar br).lo +
                        -(RatInterval3276.mul ai bi).hi| := by
                          congr 1 <;> ring
                  _ ≤ |(RatInterval3276.mul ar br).lo| +
                      |-(RatInterval3276.mul ai bi).hi| := abs_add_le _ _
                  _ = |(RatInterval3276.mul ar br).lo| +
                      |(RatInterval3276.mul ai bi).hi| := by rw [abs_neg]
        _ ≤ A * B + A * B := add_le_add hrrLo hiiHi
        _ ≤ 2 * A * B := hdouble
    · calc
        |(RatInterval3276.mul ar br).hi -
            (RatInterval3276.mul ai bi).lo| ≤
            |(RatInterval3276.mul ar br).hi| +
              |(RatInterval3276.mul ai bi).lo| := by
                calc
                  |(RatInterval3276.mul ar br).hi -
                      (RatInterval3276.mul ai bi).lo| =
                      |(RatInterval3276.mul ar br).hi +
                        -(RatInterval3276.mul ai bi).lo| := by
                          congr 1 <;> ring
                  _ ≤ |(RatInterval3276.mul ar br).hi| +
                      |-(RatInterval3276.mul ai bi).lo| := abs_add_le _ _
                  _ = |(RatInterval3276.mul ar br).hi| +
                      |(RatInterval3276.mul ai bi).lo| := by rw [abs_neg]
        _ ≤ A * B + A * B := add_le_add hrrHi hiiLo
        _ ≤ 2 * A * B := hdouble
  · apply max_le
    · calc
        |(RatInterval3276.mul ar bi).lo +
            (RatInterval3276.mul ai br).lo| ≤
            |(RatInterval3276.mul ar bi).lo| +
              |(RatInterval3276.mul ai br).lo| := abs_add_le _ _
        _ ≤ A * B + A * B := add_le_add hriLo hirLo
        _ ≤ 2 * A * B := hdouble
    · calc
        |(RatInterval3276.mul ar bi).hi +
            (RatInterval3276.mul ai br).hi| ≤
            |(RatInterval3276.mul ar bi).hi| +
              |(RatInterval3276.mul ai br).hi| := abs_add_le _ _
        _ ≤ A * B + A * B := add_le_add hriHi hirHi
        _ ≤ 2 * A * B := hdouble

end ConnesWeilRH.Dev
