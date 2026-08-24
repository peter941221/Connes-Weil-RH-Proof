import ConnesWeilRH.Source.CC20ZetaCounting

namespace ConnesWeilRH
namespace Source
namespace C1XiConjugation

open Complex
open MeasureTheory
open CC20ZetaCounting
open HurwitzZeta
open scoped ComplexConjugate

noncomputable section

private theorem hurwitzEvenFEPair_zero_f_modif_real (x : ℝ) :
    star ((HurwitzZeta.hurwitzEvenFEPair 0).f_modif x) =
      (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x := by
  simp only [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair]
  simp only [Pi.add_apply]
  change (starRingEnd ℂ) (_ + _) = _
  rw [map_add (starRingEnd ℂ)]
  congr 1
  · by_cases h : x ∈ Set.Ioi (1 : ℝ) <;>
      simp [Set.indicator, h]
  · by_cases h : x ∈ Set.Ioo (0 : ℝ) 1 <;>
      simp [Set.indicator, h]

theorem completedRiemannZeta0_conj (z : ℂ) :
    completedRiemannZeta₀ (star z) = star (completedRiemannZeta₀ z) := by
  unfold completedRiemannZeta₀ completedHurwitzZetaEven₀
  unfold WeakFEPair.Λ₀
  unfold mellin
  rw [star_div₀]
  norm_num
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only [Pi.smul_apply, smul_eq_mul, starRingEnd_apply]
  change _ = (starRingEnd ℂ) (_ * _)
  rw [map_mul (starRingEnd ℂ)]
  change _ = conj ((x : ℂ) ^ (z / 2 - 1)) * conj _
  have hcpow : conj ((x : ℂ) ^ (z / 2 - 1)) =
      (x : ℂ) ^ (star z / 2 - 1) := by
    have hcpow' := Complex.cpow_conj (x : ℂ) (z / 2 - 1) (by
      rw [Complex.arg_ofReal_of_nonneg (le_of_lt hx)]
      exact ne_of_lt Real.pi_pos)
    have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
      exact Complex.conj_ofNat 2
    convert hcpow'.symm using 1 <;> simp [Complex.conj_ofReal, htwo]
  have hreal : (starRingEnd ℂ) ((HurwitzZeta.hurwitzEvenFEPair 0).f_modif x) =
      (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x := by
    simpa only [starRingEnd_apply] using hurwitzEvenFEPair_zero_f_modif_real x
  rw [hcpow, hreal]

theorem completedRiemannXi_conj (z : ℂ) :
    completedRiemannXi (star z) = star (completedRiemannXi z) := by
  unfold completedRiemannXi
  rw [completedRiemannZeta0_conj]
  simp

#print axioms completedRiemannZeta0_conj
#print axioms completedRiemannXi_conj

end
end C1XiConjugation
end Source
end ConnesWeilRH
