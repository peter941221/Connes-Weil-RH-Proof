import ConnesWeilRH.Dev.C1BombieriSection7H

open ConnesWeilRH.Source.C1BombieriSection7H
open ConnesWeilRH.Source.C1BombieriSection7Readback

example (x y t : Real) :
    (starRingEnd ℂ) (bombieriH x y t) = bombieriH x y t := by
  unfold bombieriH
  simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal,
    bombieriKstar_star]
