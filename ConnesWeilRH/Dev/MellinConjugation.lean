import ConnesWeilRH.Dev.MellinConvolutionIdentity
import ConnesWeilRH.Dev.MellinProductCarrier
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import ConnesWeilRH.Basic

/-!
Conjugation of a real-base complex power (858).

The Hermitian-square / critical-line reality step needs `conj(x^s) = x^(conj s)` for a
positive real base `x` (exposed here as a real `c` whose complex argument is not `pi`).
This is the genuine conjugation rule; exposition later to the full Mellin transform via
`integral_conj`.  No RH is claimed; this lemma certifies the base-power conjugation side
without any sign decision.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace MellinConjugation

noncomputable section
open scoped ComplexConjugate

/-- Conjugation of a real complex base power: `conj (c^s) = c^(conj s)`.
For `c : ℝ` with non-negative argument (`arg (c:ℂ) ≠ π`), the base is its own conjugate. -/
theorem conj_cpow_of_real (c : ℝ) (s : ℂ) (hc : Complex.arg (c : ℂ) ≠ Real.pi) :
    conj ((c : ℂ) ^ s) = (c : ℂ) ^ conj s := by
  rw [Complex.cpow_conj (c : ℂ) s hc]
  rw [Complex.conj_ofReal c]

/-- The same rule specialised to the positive real base `e^t`: `conj((e^t)^s) = (e^t)^(conj s)`. -/
theorem conj_cpow_exp (t : ℝ) (s : ℂ) :
    conj ((Real.exp t : ℂ) ^ s) = (Real.exp t : ℂ) ^ conj s := by
  have harg : Complex.arg (Real.exp t : ℂ) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (Real.exp_nonneg t)]
    exact ne_of_lt Real.pi_pos
  exact conj_cpow_of_real (Real.exp t) s harg

end
end MellinConjugation
end Dev
end Source
end ConnesWeilRH
