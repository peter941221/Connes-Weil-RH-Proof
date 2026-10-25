import ConnesWeilRH.Dev.C1RouteAOwnerAnalyticTransform3092
import ConnesWeilRH.Dev.C1StripEnvelopeIbpBridge2722

/-!
# Height cost of a unit Laplace target

For a compact-log detector supported in `[-B,B]`, a unit target at `s`
forces `|Im s| <= exp(A*B) * derivOrderL1 1 f` when `|Re s| <= A`.
This excludes extending a fixed support/derivative budget to arbitrarily
high unit targets. It does not exclude rho-dependent budgets or prove RH.
-/

namespace ConnesWeilRH.Source.C1DetectorHeightCost3095

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaNearZeros
open C1ExplicitFiniteNodeCorrection
open C1StripEnvelopeIbpBridge2722
open C1G8R0OrbitGeometry
open C1RouteAOwnerAnalyticTransform3092

noncomputable section

theorem unit_laplace_target_height_le (f : CompactLogTest) (B A : Real)
    (hB : 0 ≤ B) (hsupport : Function.support f.test ⊆ Set.Icc (-B) B)
    (s : Complex) (hre : |s.re| ≤ A) (htarget : 1 ≤ ‖laplaceAt f s‖) :
    |s.im| ≤ Real.exp (A * B) * derivOrderL1 1 f := by
  have hderiv : 0 ≤ derivOrderL1 1 f := MeasureTheory.integral_nonneg
    (fun _ => norm_nonneg _)
  have hbound := norm_pow_laplaceAt_le_exp_mul_derivOrderL1 1 f B hsupport s
  simp only [pow_one] at hbound
  calc
    |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
    _ ≤ ‖s‖ * ‖laplaceAt f s‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left htarget (norm_nonneg s)
    _ ≤ Real.exp (|s.re| * B) * derivOrderL1 1 f := hbound
    _ ≤ Real.exp (A * B) * derivOrderL1 1 f :=
      mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hre hB)) hderiv

theorem no_unit_target_above_height_budget (f : CompactLogTest) (B A : Real)
    (hB : 0 ≤ B) (hsupport : Function.support f.test ⊆ Set.Icc (-B) B)
    (s : Complex) (hre : |s.re| ≤ A)
    (hheight : Real.exp (A * B) * derivOrderL1 1 f < |s.im|) :
    ¬ 1 ≤ ‖laplaceAt f s‖ := by
  intro htarget
  exact (not_lt_of_ge (unit_laplace_target_height_le f B A hB hsupport s hre htarget))
    hheight

theorem fixed_detector_unit_targets_not_unbounded
    (f : CompactLogTest) (B A : Real) (hB : 0 ≤ B)
    (hsupport : Function.support f.test ⊆ Set.Icc (-B) B) :
    ¬ (∀ T : Real, ∃ s : Complex,
      |s.re| ≤ A ∧ 1 ≤ ‖laplaceAt f s‖ ∧ T < |s.im|) := by
  intro hunbounded
  obtain ⟨s, hre, htarget, hheight⟩ :=
    hunbounded (Real.exp (A * B) * derivOrderL1 1 f)
  exact no_unit_target_above_height_budget f B A hB hsupport s hre hheight htarget

/-- This bound uses the actual selected test and its proved interpolation
value, rather than adding a unit-target premise to a substitute owner. -/
theorem selected_detector_height_le
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    |rho.1.im| ≤
      Real.exp (|rho.1.re - 1 / 2| * ((geometry.orbitIndex + 2 : Nat) : Real)) *
        derivOrderL1 1 g := by
  have hsupport : Function.support g.test ⊆
      Set.Icc (-((geometry.orbitIndex + 2 : Nat) : Real))
        (((geometry.orbitIndex + 2 : Nat) : Real)) :=
    geometry.support_bound.trans Set.Ioo_subset_Icc_self
  have htarget : 1 ≤ ‖laplaceAt g (rho.1 - 1 / 2)‖ := by
    rw [routeAOwner_laplaceAt_rho_eq_one geometry]
    simp
  simpa using unit_laplace_target_height_le g
    ((geometry.orbitIndex + 2 : Nat) : Real) |rho.1.re - 1 / 2|
    (by positivity) hsupport (rho.1 - 1 / 2) (by simp) htarget

end
end ConnesWeilRH.Source.C1DetectorHeightCost3095
