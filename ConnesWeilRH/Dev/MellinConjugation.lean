import ConnesWeilRH.Dev.MellinConvolutionIdentity
import ConnesWeilRH.Dev.MellinProductCarrier
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import ConnesWeilRH.Basic

/-!
Conjugation of a real-base complex power (858), the Mellin conjugation lemma
built on it, and the critical-line reality corollary for real-valued tests.

The Hermitian-square / critical-line reality argument needs `conj(x^s) = x^(conj s)`
for a positive real base `x`.  The log-coordinate Mellin lift
`mellinLift f s = ∫ (e^u)^s • f u` (MellinProductCarrier) then inherits the
conjugation: `conj(mellinLift f s) = mellinLift (conj ∘ f) (conj s)`, by pulling
`integral_conj` under the integral and conjugating the real-base power.

At the critical point `s = i/2`, for a **real-valued** test (`conj ∘ f = f`)
this gives `MellinLift f (-i/2) = conj (MellinLift f (i/2))`: the two Mellin
evaluations used by the route pole-pairing are complex conjugates.  That turns
the endpoint sum `Re[(M g i/2)^4] + Re[(M g -i/2)^4]` into `2*Re[(M g i/2)^4]`
(one real statement), but does **not** decide that statement's sign, which
remains a genuine analytic input.

No RH is claimed; these lemmas certify the conjugation/reality side of the
critical-line direction without any sign decision.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace MellinConjugation

noncomputable section
open MeasureTheory
open scoped ComplexConjugate Topology

/-- Conjugation of a real complex base power: `conj (c^s) = c^(conj s)`.
For `c : ℝ` with non-negative argument (`arg (c:ℂ) ≠ π`), the base is its own
conjugate. -/
theorem conj_cpow_of_real (c : ℝ) (s : ℂ) (hc : Complex.arg (c : ℂ) ≠ Real.pi) :
    conj ((c : ℂ) ^ s) = (c : ℂ) ^ conj s := by
  rw [Complex.cpow_conj (c : ℂ) s hc]
  simp [Complex.conj_ofReal]

/-- Conjugation of the positive-real base power `e^t`: `conj((e^t)^s) = (e^t)^(conj s)`. -/
theorem conj_cpow_exp (t : ℝ) (s : ℂ) :
    conj ((Real.exp t : ℂ) ^ s) = (Real.exp t : ℂ) ^ conj s := by
  have harg : Complex.arg (Real.exp t : ℂ) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (Real.exp_nonneg t)]
    exact ne_of_lt Real.pi_pos
  exact conj_cpow_of_real (Real.exp t) s harg

/-- Conjugation distributes over the Mellin weight times a value. -/
theorem conj_smul_cpow_exp (u : ℝ) (s z : ℂ) :
    conj ((Real.exp u : ℂ) ^ s • z) = (Real.exp u : ℂ) ^ conj s • conj z := by
  rw [smul_eq_mul, smul_eq_mul, map_mul, conj_cpow_exp u s]

/-- Conjugation commutes with the Mellin lift on the log-additive carrier:
   `conj(mellinLift f s) = mellinLift (conj ∘ f) (conj s)`. -/
theorem mellinLift_conj (f : ℝ → ℂ) (s : ℂ) :
    conj (MellinProductCarrier.mellinLift f s) =
      MellinProductCarrier.mellinLift (fun x : ℝ => conj (f x)) (conj s) := by
  unfold MellinProductCarrier.mellinLift
  rw [MellinConvolutionIdentity.mellin_comp_log_eq_exp_integral f]
  rw [← integral_conj (f := fun t : ℝ => (Real.exp t : ℂ) ^ s • f t)]
  rw [MellinConvolutionIdentity.mellin_comp_log_eq_exp_integral
    (fun x : ℝ => conj (f x)) (conj s)]
  apply integral_congr_ae
  filter_upwards with t
  exact conj_smul_cpow_exp t s (f t)

/-- Conjugation of the critical-point half imaginary unit: `conj (i/2) = -i/2`. -/
lemma conj_I_half : conj (Complex.I / 2 : ℂ) = - (Complex.I / 2 : ℂ) := by
  rw [div_eq_mul_inv, map_mul, map_inv₀, Complex.conj_ofNat, Complex.conj_I]
  ring

/-- **Critical-line reality for a real-valued test**: `MellinLift g (-i/2) =
   conj (MellinLift g (i/2))` when `conj (g x) = g x` for all `x`. -/
theorem mellinLift_real_involution (g : ℝ → ℂ) (hg : ∀ x : ℝ, conj (g x) = g x) :
    MellinProductCarrier.mellinLift g (- (Complex.I / 2 : ℂ)) =
      conj (MellinProductCarrier.mellinLift g (Complex.I / 2 : ℂ)) := by
  have hm := mellinLift_conj g (Complex.I / 2 : ℂ)
  rw [conj_I_half] at hm
  have hdec : (fun x : ℝ => conj (g x)) = g := by funext x; exact hg x
  rw [hdec] at hm
  exact Eq.symm hm

end
end MellinConjugation
end Dev
end Source
end ConnesWeilRH





