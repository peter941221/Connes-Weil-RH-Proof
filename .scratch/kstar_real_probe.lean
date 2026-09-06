import ConnesWeilRH.Dev.C1BombieriSection7Readback

open ConnesWeilRH.Source.C1BombieriSection7Readback
open scoped ComplexConjugate

#check Complex.conj_ofReal
#check Complex.star_def
#check map_neg
#check Complex.conj_I
#check starRingEnd_apply

example (x y t : Real) :
    (starRingEnd ℂ) (bombieriKstar x y t) = bombieriKstar x y t := by
  unfold bombieriKstar
  simp only [map_sub, map_mul, map_div₀, map_add, map_ofNat,
    ConnesWeilRH.Source.C1BombieriSection7Readback.bombieriK_star,
    ← starRingEnd_apply, Complex.conj_ofReal, Complex.conj_I]
  have h1 : (↑t : Complex) * (-Complex.I / 2 - (↑y : Complex)) =
      -((↑t : Complex) * (Complex.I / 2 + (↑y : Complex))) := by ring
  have h2 : (↑t : Complex) * (-Complex.I / 2 + (↑x : Complex)) =
      -((↑t : Complex) * (Complex.I / 2 - (↑x : Complex))) := by ring
  have h3 : (↑t : Complex) * (-Complex.I / 2 + (↑y : Complex)) =
      -((↑t : Complex) * (Complex.I / 2 - (↑y : Complex))) := by ring
  have h4 : (↑t : Complex) * (-Complex.I / 2 - (↑x : Complex)) =
      -((↑t : Complex) * (Complex.I / 2 + (↑x : Complex))) := by ring
  rw [h1, h2, h3, h4, bombieriK_neg, bombieriK_neg,
    bombieriK_neg, bombieriK_neg]
  ring
