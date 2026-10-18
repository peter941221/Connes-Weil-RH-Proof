import Mathlib.Analysis.SpecialFunctions.Exp

namespace ConnesWeilRH.Dev

theorem routeBExpFactorBounds2938 {x a b : ℝ}
    (ha : a ≤ x) (hb : x ≤ b) :
    Real.exp a ≤ Real.exp x ∧ Real.exp x ≤ Real.exp b := by
  exact ⟨Real.exp_le_exp.mpr ha, Real.exp_le_exp.mpr hb⟩

end ConnesWeilRH.Dev
