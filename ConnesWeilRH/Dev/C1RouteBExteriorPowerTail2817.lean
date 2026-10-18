import ConnesWeilRH.Dev.C1RouteBExteriorPowerIntegrability2816
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open MeasureTheory Set

theorem routeB_exterior_power_tail2817
    {f : ℝ → ℝ} {C T a : ℝ}
    (hC : 0 ≤ C) (hT : 0 < T) (ha : a < -1)
    (hmeas : AEStronglyMeasurable f (volume.restrict (Set.Ioi T)))
    (hbound : ∀ x ∈ Set.Ioi T, ‖f x‖ ≤ C * x ^ a) :
    ‖∫ x in Set.Ioi T, f x‖ ≤ C * (-T ^ (a + 1) / (a + 1)) := by
  have hfint : IntegrableOn f (Set.Ioi T) :=
    routeB_exterior_power_integrable2816 hC hT ha hmeas hbound
  have hpow : IntegrableOn (fun x : ℝ => x ^ a) (Set.Ioi T) :=
    integrableOn_Ioi_rpow_of_lt ha hT
  have hmajor : IntegrableOn (fun x : ℝ => C * x ^ a) (Set.Ioi T) :=
    hpow.const_mul C
  calc
    ‖∫ x in Set.Ioi T, f x‖ ≤ ∫ x in Set.Ioi T, ‖f x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x in Set.Ioi T, C * x ^ a :=
      integral_mono_ae hfint.norm hmajor (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact hbound x hx)
    _ = C * (-T ^ (a + 1) / (a + 1)) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt ha hT]

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
