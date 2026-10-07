import ConnesWeilRH.Dev.C1RouteACorrectionIntervalPropagation2598

namespace ConnesWeilRH.Dev

theorem rectL1Upper2598_le_of_coordinate_bounds2617
    (r : ComplexRect2427) (realBound imagBound : ℝ) (upper : NNReal)
    (hreLo : |r.reLo| ≤ realBound) (hreHi : |r.reHi| ≤ realBound)
    (himLo : |r.imLo| ≤ imagBound) (himHi : |r.imHi| ≤ imagBound)
    (htotal : realBound + imagBound ≤ (upper : ℝ)) :
    rectL1Upper2598 r ≤ upper := by
  change max |r.reLo| |r.reHi| + max |r.imLo| |r.imHi| ≤ (upper : ℝ)
  exact (add_le_add (max_le hreLo hreHi) (max_le himLo himHi)).trans htotal

end ConnesWeilRH.Dev
