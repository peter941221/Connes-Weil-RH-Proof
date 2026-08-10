import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import ConnesWeilRH.Dev.ArchPhaseZFourthNonneg

/-!
GammaArgLeaf: finite-S arch-one sign as a function of the single open Gamma-arg.

Given the (open, new-math) analytic premise `harg`, the finite-S arch sign
`0 <= Re[(Gamma(1+i/2))^4]` closes axiom-clean by `ArchPhaseZFourthNonneg`.
mathlib has no Stirling/arg-Gamma; Complex.Gamma is non-computable, so `harg` is
NOT derived here. RH NOT claimed. -/
namespace ConnesWeilRH
namespace Dev
namespace GammaArgLeaf


open ConnesWeilRH.Source.Dev.ArchPhaseZFourthNonneg

-- The base point complex on the arch. -
noncomputable def archZ : Complex := Complex.Gamma (1 + Complex.I / 2)

/-- The precise finite-S sign at a=1, as a direct function of the open Gamma-arg. -/
theorem gammaSign_at_one
    (harg : |(Complex.Gamma (1 + Complex.I / 2)).arg| < Real.pi / 8) :
    0 ≤ (Complex.Gamma (1 + Complex.I / 2) ^ 4).re := by
  let z : ℂ := Complex.Gamma (1 + Complex.I / 2)
  have hre : 0 < (1 + Complex.I / 2 : ℂ).re := by norm_num
  have hz : z ≠ 0 := by
    dsimp [z]
    exact Complex.Gamma_ne_zero_of_re_pos hre
  exact re_pow4_nonneg_of_abs_arg_lt_pi_eighth hz harg

end GammaArgLeaf
end Dev
end ConnesWeilRH
