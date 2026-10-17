import ConnesWeilRH.Dev.C1RouteAIntervalAlgebra
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ConnesWeilRH.Dev

open MeasureTheory
noncomputable section

theorem intervalIntegral_norm_le_endpointAbsMax2769
    {a b : ℝ} (hab : a ≤ b) (B : RealInterval2429)
    {f : ℝ → ℝ} (hf : Continuous f)
    (hmem : ∀ x ∈ Set.Icc a b, B.Mem (f x)) :
    (∫ x in a..b, ‖f x‖) ≤ (b - a) * B.endpointAbsMax := by
  have hfi : IntervalIntegrable (fun x => ‖f x‖) volume a b :=
    (continuous_norm.comp hf).intervalIntegrable _ _
  have hgi : IntervalIntegrable (fun _ : ℝ => B.endpointAbsMax) volume a b :=
    continuous_const.intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on
    (f := fun x => ‖f x‖) (g := fun _ : ℝ => B.endpointAbsMax)
    hab hfi hgi (fun x hx => by
      simpa only [Real.norm_eq_abs] using
        (abs_le_max_abs_abs (hmem x hx).1 (hmem x hx).2))
  have hconst :
      (∫ _x in a..b, B.endpointAbsMax) =
        (b - a) * B.endpointAbsMax := by
    simp [intervalIntegral.integral_const, smul_eq_mul]
  rw [hconst] at hmono
  exact hmono

end
end ConnesWeilRH.Dev
