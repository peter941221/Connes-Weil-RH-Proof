import ConnesWeilRH.Dev.Wall14PlateauFDeriv
import ConnesWeilRH.Dev.Wall14PlateauExplicitF
import ConnesWeilRH.Dev.Wall14PlateauProbe
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral

open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
namespace ConnesWeilRH.Source.Dev.Wall14Plateau

/-- For 0 <= y <= 1, e^{y/2} - 1 <= (y/2) * e^{1/2}. -/
lemma exp_sub_one_le (y : ℝ) (hy0 : 0 <= y) (hy1 : y <= 1) :
    Real.exp (y / 2) - 1 <= (y / 2) * Real.exp (1 / 2 : ℝ) := by
  let f : ℝ → ℝ := Real.exp
  have hderiv : deriv f = f := by
    funext x; exact (Real.hasDerivAt_exp x).deriv
  have hdiff : ∀ x ∈ Set.uIcc (0 : ℝ) (y / 2), DifferentiableAt ℝ f x :=
    fun x hx => (Real continuous / hasDerivAt_exp x).differentiableAt
  have hcont : ContinuousOn f (Set.uIcc (0 : ℝ) (y / 2)) := Real.continuous_exp.continuousOn
  have hFTC := intervalIntegral.integral_deriv_eq_sub' f hderiv hdiff hcont
  -- hFTC : ∫ x in 0..y/2, f x = f (y/2) - f 0 = exp(y/2)-1
  have h1 : Real.exp (y / 2) - 1 = ∫ x in (0 : ℝ)..(y / 2), Real.exp x := by
    simpa [f] using hFTC.symm
  have hmono := intervalIntegral.integral_mono_on (f := Real.exp)
    (g := fun _ : ℝ => Real.exp (1 / 2 : ℝ))
    (a := (0:ℝ)) (b := (y/2))
    (by intro x hx; rw [Real.exp_le_exp]; linarith [hy1, hx.1, hx.2])
  have h2 : (∫ x in (0 : ℝ)..(y / 2), Real.exp (1 / 2 : ℝ)) = (y / 2) * Real.exp (1 / 2 : ℝ) := by
    rw [intervalIntegral.integral_const]; ring
  calc
    Real.exp (y / 2) - 1 <= ∫ x in (0 : ℝ)..(y / 2), Real.exp x := by rw [h1]; exact le_of_eq h1.symm
    _ <= (y / 2) * Real.exp (1 / 2 : ℝ) := by
      rw [← h2]; exact hmono

end ConnesWeilRH.Source.Dev.Wall14Plateau