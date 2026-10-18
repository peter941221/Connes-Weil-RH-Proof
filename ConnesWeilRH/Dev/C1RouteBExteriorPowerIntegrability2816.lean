import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open MeasureTheory Set

theorem routeB_exterior_power_integrable2816
    {f : ℝ → ℝ} {C T a : ℝ}
    (hC : 0 ≤ C) (hT : 0 < T) (ha : a < -1)
    (hmeas : AEStronglyMeasurable f (volume.restrict (Set.Ioi T)))
    (hbound : ∀ x ∈ Set.Ioi T, ‖f x‖ ≤ C * x ^ a) :
    IntegrableOn f (Set.Ioi T) := by
  have hpow : IntegrableOn (fun x : ℝ => x ^ a) (Set.Ioi T) :=
    integrableOn_Ioi_rpow_of_lt ha hT
  have hmajor : IntegrableOn (fun x : ℝ => C * x ^ a) (Set.Ioi T) :=
    hpow.const_mul C
  exact hmajor.mono' hmeas (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hbound x hx)

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
