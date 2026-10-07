import ConnesWeilRH.Dev.C1RouteAAnalyticMomentSystem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped Interval
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def normalizedMomentIntegrand2618
    (modulation radius : ℝ) (node : ℂ) (coordinate : ℝ) : ℂ :=
  if |coordinate| < 1 then
    Complex.exp ((-30 / (1 - coordinate ^ 2) : ℝ) +
      (node + (modulation : ℂ) * Complex.I) * (radius : ℂ) * (coordinate : ℂ))
  else 0

theorem momentIntegrand2351_support_subset_Ioc2618
    (modulations : Fin 30 → ℝ) (index : Fin 30) (node : ℂ) :
    Function.support (fun position : ℝ =>
      Complex.exp (node * (position : ℂ)) * momentFamily2351 modulations index position) ⊆
      Set.Ioc (-(storedWidth index ^ 2)) (storedWidth index ^ 2) := by
  intro position hposition
  have hinside : |position| < storedWidth index ^ 2 := by
    by_contra houtside
    exact hposition (by simp [momentFamily2351, externalFamilyValue2344, houtside])
  exact ⟨(abs_lt.mp hinside).1, (abs_lt.mp hinside).2.le⟩

theorem momentEntry2351_eq_intervalIntegral2618
    (modulations : Fin 30 → ℝ) (index : Fin 30) (node : ℂ) :
    momentEntry2351 modulations index node =
      ∫ position in (-(storedWidth index ^ 2))..(storedWidth index ^ 2),
        Complex.exp (node * (position : ℂ)) * momentFamily2351 modulations index position := by
  exact (intervalIntegral.integral_eq_integral_of_support_subset
    (momentIntegrand2351_support_subset_Ioc2618 modulations index node)).symm

theorem scaledMomentIntegrand2351_eq_normalized2618
    (modulations : Fin 30 → ℝ) (index : Fin 30) (node : ℂ) (coordinate : ℝ) :
    Complex.exp (node * ((storedWidth index ^ 2 * coordinate : ℝ) : ℂ)) *
      momentFamily2351 modulations index (storedWidth index ^ 2 * coordinate) =
      normalizedMomentIntegrand2618 (modulations index) (storedWidth index ^ 2)
        node coordinate := by
  have hradius : 0 < storedWidth index ^ 2 := pow_pos (storedWidth_pos index) 2
  have hguard : |storedWidth index ^ 2 * coordinate| < storedWidth index ^ 2 ↔
      |coordinate| < 1 := by
    rw [abs_mul, abs_of_pos hradius]
    constructor <;> intro hbound <;> nlinarith
  by_cases hinside : |coordinate| < 1
  · have hphysical := hguard.mpr hinside
    simp only [momentFamily2351, externalFamilyValue2344, if_pos hphysical,
      normalizedMomentIntegrand2618, if_pos hinside, one_mul,
      mul_div_cancel_left₀ coordinate (ne_of_gt hradius),
      Complex.ofReal_mul]
    rw [← Complex.exp_add]
    congr 1
    ring
  · have hphysical : ¬ |storedWidth index ^ 2 * coordinate| < storedWidth index ^ 2 :=
      fun hbound => hinside (hguard.mp hbound)
    simp only [momentFamily2351, externalFamilyValue2344, if_neg hphysical,
      normalizedMomentIntegrand2618, if_neg hinside, mul_zero]

theorem momentEntry2351_eq_normalizedIntegral2618
    (modulations : Fin 30 → ℝ) (index : Fin 30) (node : ℂ) :
    momentEntry2351 modulations index node =
      (storedWidth index ^ 2) •
        ∫ coordinate in (-1 : ℝ)..1,
          normalizedMomentIntegrand2618 (modulations index) (storedWidth index ^ 2)
            node coordinate := by
  rw [momentEntry2351_eq_intervalIntegral2618]
  have hchange := intervalIntegral.smul_integral_comp_mul_left
    (fun position : ℝ => Complex.exp (node * (position : ℂ)) *
      momentFamily2351 modulations index position)
    (a := (-1 : ℝ)) (b := 1) (storedWidth index ^ 2)
  simp only [mul_neg_one, mul_one] at hchange
  rw [← hchange]
  congr 1
  apply intervalIntegral.integral_congr
  intro coordinate _
  exact scaledMomentIntegrand2351_eq_normalized2618 modulations index node coordinate

noncomputable def realNormalizedMomentIntegrand2618
    (radius nodeReal coordinate : ℝ) : ℝ :=
  if |coordinate| < 1 then
    Real.exp (-30 / (1 - coordinate ^ 2) + nodeReal * radius * coordinate)
  else 0

theorem normalizedMomentIntegrand2618_eq_real_of_phase_cancel
    (modulation radius : ℝ) (node : ℂ) (hphase : node.im + modulation = 0)
    (coordinate : ℝ) :
    normalizedMomentIntegrand2618 modulation radius node coordinate =
      (realNormalizedMomentIntegrand2618 radius node.re coordinate : ℂ) := by
  have hreal : node + (modulation : ℂ) * Complex.I = (node.re : ℂ) := by
    apply Complex.ext <;> simp [hphase]
  unfold normalizedMomentIntegrand2618 realNormalizedMomentIntegrand2618
  rw [hreal]
  split_ifs <;> simp [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_exp]

theorem momentEntry2351_eq_realIntegral_of_phase_cancel2618
    (modulations : Fin 30 → ℝ) (index : Fin 30) (node : ℂ)
    (hphase : node.im + modulations index = 0) :
    momentEntry2351 modulations index node =
      ((storedWidth index ^ 2 *
        ∫ coordinate in (-1 : ℝ)..1,
          realNormalizedMomentIntegrand2618 (storedWidth index ^ 2) node.re coordinate : ℝ) : ℂ) := by
  rw [momentEntry2351_eq_normalizedIntegral2618]
  simp_rw [normalizedMomentIntegrand2618_eq_real_of_phase_cancel _ _ _ hphase]
  rw [intervalIntegral.integral_ofReal]
  simp [Complex.real_smul, Complex.ofReal_mul]

theorem momentEntry2351_im_eq_zero_of_phase_cancel2618
    (modulations : Fin 30 → ℝ) (index : Fin 30) (node : ℂ)
    (hphase : node.im + modulations index = 0) :
    (momentEntry2351 modulations index node).im = 0 := by
  rw [momentEntry2351_eq_realIntegral_of_phase_cancel2618 _ _ _ hphase]
  exact Complex.ofReal_im _

end ConnesWeilRH.Dev
