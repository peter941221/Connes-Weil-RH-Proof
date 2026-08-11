import ConnesWeilRH.Dev.Wall14PlateauFDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

namespace ConnesWeilRH.Source.Dev.Wall14Plateau

open MeasureTheory Filter Set
open scoped Topology Interval

/-- If `f = 0` on the open interval `(a,b)`, the interval integral is zero. -/
theorem interval_integral_eq_zero_of_Ioo {a b : ℝ} (ha : a < b) {f : ℝ → ℝ}
    (hf : ∀ x, a < x → x < b → f x = 0) :
    (∫ x in a..b, f x) = 0 := by
  rw [intervalIntegral.integral_of_le (le_of_lt ha)]
  have hset : Ioo a b =ᵐ[volume] Ioc a b := by
    simpa using (MeasureTheory.Ioo_ae_eq_Ioc (μ := (volume : Measure ℝ)) (a := a) (b := b))
  calc
    (∫ x in (Ioc a b : Set ℝ), f x ∂volume)
        = ∫ x in (Ioo a b), f x ∂volume := (setIntegral_congr_set hset).symm
    _ = ∫ x in (Ioo a b), (fun _ : ℝ => (0 : ℝ)) x ∂volume := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro x hx; exact hf x hx.1 hx.2
    _ = 0 := by simp

end ConnesWeilRH.Source.Dev.Wall14Plateau
