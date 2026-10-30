import ConnesWeilRH.Dev.C1RouteASignedAggregateCell2539
import ConnesWeilRH.Dev.C1RouteAOwnerWindowZeroExtension3201

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped BigOperators ContDiff

theorem weightedExternal3201_eq_weightedPhysical2539_re
    (sigma : ℝ) (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) :
    weightedExternal3201 sigma coefficients modulations =
      fun position =>
        (weightedPhysical2539 sigma coefficients modulations position).re := by
  funext position
  simp only [weightedExternal3201, weightedPhysical2539, weightedFunction2348,
    weightedExp2348, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    zero_mul, sub_zero]

theorem weightedExternal3201_continuous
    (sigma : ℝ) (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) :
    Continuous (weightedExternal3201 sigma coefficients modulations) := by
  rw [weightedExternal3201_eq_weightedPhysical2539_re]
  exact Complex.continuous_re.comp
    (weightedPhysical2539_contDiff sigma coefficients modulations).continuous

theorem weightedExternal3201_intervalIntegrable
    (sigma : ℝ) (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ)
    (left right : ℝ) :
    IntervalIntegrable
      (weightedExternal3201 sigma coefficients modulations) volume left right := by
  exact (weightedExternal3201_continuous sigma coefficients modulations).intervalIntegrable
    left right

end ConnesWeilRH.Dev