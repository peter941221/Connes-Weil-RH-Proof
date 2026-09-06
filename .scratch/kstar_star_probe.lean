import ConnesWeilRH.Dev.C1BombieriSection7Readback

open ConnesWeilRH.Source.C1BombieriSection7Readback
open scoped ComplexConjugate

example (z : Complex) :
    (starRingEnd ℂ) (bombieriK z) = bombieriK ((starRingEnd ℂ) z) := by
  unfold bombieriK
  by_cases hz : z = 0
  · simp [hz]
  · have hsz : (starRingEnd ℂ) z ≠ 0 := star_ne_zero.mpr hz
    rw [if_neg hz, if_neg hsz]
    rw [map_div₀, ← Complex.sin_conj]
