import ConnesWeilRH.Dev.C1RouteBThetaTSharper2996

namespace ConnesWeilRH.Dev

/- Coordinate form of the sharp theta enclosure.  The quotient proof consumes
   real bounds, so expose them once at the boundary of the complex rectangle. -/
theorem routeBThetaTSharperCoordinates2998 {δ : ℝ}
    (hδlo : Real.pi / 192 ≤ δ)
    (hδhi : δ ≤ Real.pi / 192 + Real.pi / 1024) :
    ((255 : ℝ) / 10000 ≤
        (routeBThetaTSharper2996 (5 * Real.pi / 3 + δ)).re) ∧
      ((routeBThetaTSharper2996 (5 * Real.pi / 3 + δ)).re ≤
        (26 : ℝ) / 1000) ∧
      (-(43 : ℝ) / 1000 ≤
        (routeBThetaTSharper2996 (5 * Real.pi / 3 + δ)).im) ∧
      ((routeBThetaTSharper2996 (5 * Real.pi / 3 + δ)).im ≤
        -(425 : ℝ) / 10000) := by
  have h := routeBThetaTSharperMem2996 hδlo hδhi
  change ((255 : ℝ) / 10000 ≤
      (routeBThetaTSharper2996 (5 * Real.pi / 3 + δ)).re) ∧
    ((routeBThetaTSharper2996 (5 * Real.pi / 3 + δ)).re ≤
      (26 : ℝ) / 1000) ∧
    (-(43 : ℝ) / 1000 ≤
      (routeBThetaTSharper2996 (5 * Real.pi / 3 + δ)).im) ∧
    ((routeBThetaTSharper2996 (5 * Real.pi / 3 + δ)).im ≤
      -(425 : ℝ) / 10000) at h
  exact h

end ConnesWeilRH.Dev
