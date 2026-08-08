import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import ConnesWeilRH.Dev.ArctanCert
import ConnesWeilRH.Dev.SSeriesSandwich

open scoped ComplexConjugate

noncomputable section

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace PhaseGateSandwich

-- Arch-phase shift:  D = S - gamma/2 - atan(1/2).
-- The real-phase gate |arg Gamma(1+I/2)| <= pi/8 reduces to |D| < pi/8 plus the
-- (open, separately documented) Gamma magnitude identity.  This file closes |D|:
--        -pi/8 < D < pi/8
-- axiom-clean, using only mathlib bounds for gamma (0.5 < gamma < 2/3) and pi
-- (pi > 3) and the in-repo atan(1/2) and S-series bounds we proved already.

/-- The arch-phase shift of the C2 gate. -/
def D : Real :=
  SSandwich.S - (Real.eulerMascheroniConstant / 2) - Real.arctan (1 / 2)

/-- gamma/2 <= (2/3)/2  (from gamma < 2/3, mathlib). -/
lemma gamma_two_thirds : (Real.eulerMascheroniConstant / 2) <= (2 / 3 : Real) / 2 := by
  have hg : Real.eulerMascheroniConstant < (2 / 3 : Real) :=
    Real.eulerMascheroniConstant_lt_two_thirds
  linarith

/-- 1/4 <= gamma/2  (from 1/2 < gamma, mathlib). -/
lemma gamma_two_lower : (1 / 4 : Real) <= Real.eulerMascheroniConstant / 2 := by
  have hg : (1 / 2 : Real) < Real.eulerMascheroniConstant :=
    Real.one_half_lt_eulerMascheroniConstant
  linarith

/-- 8/3 < pi  (pi > 3 in mathlib). -/
lemma eightThirds_lt_pi : (8 / 3 : Real) < Real.pi := by
  have hp : (3 : Real) < Real.pi := Real.pi_gt_three
  nlinarith

/-- 1/3 < pi/8. -/
lemma halfThirds_lt_pi_eighth : (1 / 3 : Real) < Real.pi / 8 := by
  nlinarith [eightThirds_lt_pi]

/-- lower gate: `-pi/8 < D`. -/
theorem D_lower : -(Real.pi / 8) < D := by
  have hS : (1 / 2 : Real) <= SSandwich.S := SSandwich.S_ge_half
  have hg := gamma_two_thirds
  have hat : Real.arctan (1 / 2) <= (1 / 2 : Real) := (ArctanCert.arctan_half).2
  have hlo : -(1 / 3 : Real) <= D := by
    dsimp [D]
    linarith
  have hord : -(Real.pi / 8) < -(1 / 3 : Real) := by
    have htp : (1 / 3 : Real) < Real.pi / 8 := halfThirds_lt_pi_eighth
    linarith
  exact lt_of_lt_of_le hord hlo

/-- upper bound: `D < pi/8`. -/
theorem D_upper : D < Real.pi / 8 := by
  have hS : SSandwich.S <= (1 / 2 : Real) + (1 / 32) := SSandwich.S_le_half_plus
  have hg := gamma_two_lower
  have hat : (2 / 5 : Real) <= Real.arctan (1 / 2) := (ArctanCert.arctan_half).1
  have hup : D <= (1 / 3 : Real) := by
    dsimp [D]
    linarith
  exact lt_of_le_of_lt hup halfThirds_lt_pi_eighth

/-- absolute bound: `|D| < pi/8`. -/
theorem D_abs_lt_pi_eighth : abs D < Real.pi / 8 := by
  exact abs_lt.mpr ⟨D_lower, D_upper⟩


/-- Gamma conjugation at `1 + I/2`:  Gamma(1 - I/2) = conj (Gamma (1 + I/2)). -/
theorem gamma_conj_half :
    Complex.Gamma (conj ((1 : Complex) + Complex.I / 2)) =
      conj (Complex.Gamma ((1 : Complex) + Complex.I / 2)) := by
  exact Complex.Gamma_conj ((1 : Complex) + Complex.I / 2)

end PhaseGateSandwich
end Dev
end Source
end ConnesWeilRH
end
