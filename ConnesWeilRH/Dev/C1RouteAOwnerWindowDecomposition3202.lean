import ConnesWeilRH.Dev.C1RouteAOwnerWindowZeroExtension3201

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

/--
The slightly enlarged diagnostic window has the same weighted owner integral
as the exact owner support window. The outer pieces are zero by 3201; the
three interval-integrability hypotheses keep the adjacent-interval identities
explicit rather than hiding them in a numerical claim.
-/
theorem intervalIntegral_weightedExternal_eq_ownerWindow3202
    (sigma : ℝ) (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ)
    (hleft : IntervalIntegrable
      (weightedExternal3201 sigma coefficients modulations) volume
      (-diagnosticRadius3201) (-(storedWidth 4 ^ 2)))
    (hinner : IntervalIntegrable
      (weightedExternal3201 sigma coefficients modulations) volume
      (-(storedWidth 4 ^ 2)) (storedWidth 4 ^ 2))
    (hright : IntervalIntegrable
      (weightedExternal3201 sigma coefficients modulations) volume
      (storedWidth 4 ^ 2) diagnosticRadius3201) :
    (∫ position in (-diagnosticRadius3201)..diagnosticRadius3201,
      weightedExternal3201 sigma coefficients modulations position) =
      ∫ position in (-(storedWidth 4 ^ 2))..(storedWidth 4 ^ 2),
        weightedExternal3201 sigma coefficients modulations position := by
  have hleft_inner := hleft.trans hinner
  have hleft_identity := intervalIntegral.integral_add_adjacent_intervals
    hleft hinner
  have hfull_identity := intervalIntegral.integral_add_adjacent_intervals
    hleft_inner hright
  have hleft_zero := intervalIntegral_weightedExternal_zero_on_diagnostic_left3201
    sigma coefficients modulations
  have hright_zero := intervalIntegral_weightedExternal_zero_on_diagnostic_right3201
    sigma coefficients modulations
  linarith

end ConnesWeilRH.Dev