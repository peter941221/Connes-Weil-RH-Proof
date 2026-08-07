import ConnesWeilRH.Dev.MellinConvolutionIdentity
import ConnesWeilRH.Dev.MellinProductCarrier
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import ConnesWeilRH.Basic

/-!
Conjugation of a real-base complex power (858), and the Mellin conjugation
lemma built on it.

The Hermitian-square / critical-line reality step needs `conj(x^s) = x^(conj s)`
for a positive real base `x`.  The log-coordinate Mellin lift
`mellinLift f s = ∫ (e^u)^s • f u` (MellinProductCarrier) then inherits the
conjugation: `conj(mellinLift f s) = mellinLift (conj ∘ f) (conj s)`, by pulling
`integral_conj` under the integral and conjugating the real-base power.

No RH is claimed; this certifies the base-power conjugation side and the
integral conjugation step for the critical-line reality direction, without any
sign decision.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace MellinConjugation

noncomputable section
open MeasureTheory
open Complex
open scoped ComplexConjugate Topology

/-- Conjugation of a real complex base power: `conj (c^s) = c^(conj s)`.
For `c : ℝ` with non-negative argument (`arg (c:ℂ) ≠ π`), the base is its own
conjugate. -/
theorem conj_cpow_of_real (c : ℝ) (s : ℂ) (hc : Complex.arg (c : ℂ) ≠ Real.pi) :
    conj ((c : ℂ) ^ s) = (c : ℂ) ^ conj s := by
  rw [Complex.cpow_conj (c : ℂ) s hc]
  rw [Complex.conj_ofReal c]

/-- Conjugation of the positive-real base power `e^t`: `conj((e^t)^s) = (e^t)^(conj s)`. -/
theorem conj_cpow_exp (t : ℝ) (s : ℂ) :
    conj ((Real.exp t : ℂ) ^ s) = (Real.exp t : ℂ) ^ conj s := by
  have harg : Complex.arg (Real.exp t : ℂ) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (Real.exp_nonneg t)]
    exact ne_of_lt Real.pi_pos
  exact conj_cpow_of_real (Real.exp t) s harg

/-- Conjugation distributes over the Mellin weight times a value:
   `conj ((e^u)^s • z) = (e^u)^(conj s) • conj z`. -/
theorem conj_smul_cpow_exp (u : ℝ) (s z : ℂ) :
    conj ((Real.exp u : ℂ) ^ s • z) = (Real.exp u : ℂ) ^ (conj s) • conj z := by
  rw [smul_eq_mul, smul_eq_mul]
  rw [map_mul]
  rw [conj_cpow_exp u s]

/-- Conjugation commutes with the Mellin lift on the log-additive carrier:
   `conj(mellinLift f s) = mellinLift (conj ∘ f) (conj s)`.

This is the integral part of the critical-line reality step: conjugate the
Mellin integral, push the conjugate onto the integrand and the exponent.  It
does **not** by itself decide the sign of the fourth-power endpoint. -/
theorem mellinLift_conj (f : ℝ → ℂ) (s : ℂ) :
    conj (MellinProductCarrier.mellinLift f s) =
      MellinProductCarrier.mellinLift (fun x : ℝ => conj (f x)) (conj s) := by
  unfold MellinProductCarrier.mellinLift
  rw [MellinConvolutionIdentity.mellin_comp_log_eq_exp_integral f]
  rw [← integral_conj (f := fun u : ℝ => (Real.exp u : ℂ) ^ s • f u)]
  rw [MellinConvolutionIdentity.mellin_comp_log_eq_exp_integral
    (fun x : ℝ => conj (f x)) (conj s)]
  apply integral_congr_ae
  filter_upwards with u
  exact conj_smul_cpow_exp u s (f u)

end
end MellinConjugation
end Dev
end Source
end ConnesWeilRH
