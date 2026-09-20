/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3AnnularTwoIBP
import ConnesWeilRH.Dev.C1G8R3CriticalMellinSecondDerivative

/-!
# Concrete CCM24 critical-profile input for the annular tail

This is the first instantiation step after the abstract two-IBP estimate:
the actual critical Mellin profile is supplied as `theta`, with its first
and second logarithmic derivatives read back from the carrier and the landed
second-chain-rule leaf.  The theorem still leaves the scattering multiplier
product as a separate consumer; it does not identify that product by fiat.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open MeasureTheory Complex

theorem annular_ccm24CriticalMellinLogProfile_v_tail_le
    (f : SchwartzMap ℝ ℂ) {v : ℝ → ℂ}
    (hv : Measurable v)
    (hvint : ∀ s : ℝ, v s = ∫ ξ : ℝ,
      ccm24CriticalMellinLogProfile f ξ *
        cexp ((ξ : ℂ) * (ofReal (-2 * Real.pi * s) * I)))
    {X : ℝ} (hX : 0 < X) :
    (∫⁻ s in Set.Ici X, ENNReal.ofReal (s * ‖v s‖ ^ 2))
      ≤ ENNReal.ofReal
        ((∫ ξ : ℝ,
          ‖ccm24CriticalMellinLogProfileSecondDerivFormula f ξ‖) ^ 2 /
            (32 * Real.pi ^ 4 * X ^ 2)) := by
  refine annular_v_tail_lintegral_le_of_two_ibp
    (v := v) (θ := ccm24CriticalMellinLogProfile f)
    (θ' := ccm24CriticalMellinLogProfileFirstDerivFormula f)
    (θ'' := ccm24CriticalMellinLogProfileSecondDerivFormula f)
    hv hvint ?_ ?_ ?_ ?_ ?_ hX
  · intro ξ
    simpa [ccm24CriticalMellinLogProfileFirstDerivFormula,
      ccm24CriticalMellinLogProfile,
      ccm24CriticalMellinLogProfileChainDeriv, smul_eq_mul,
      mul_assoc, mul_left_comm, mul_comm] using
      (hasDerivAt_ccm24CriticalMellinLogProfile f ξ)
  · intro ξ
    change HasDerivAt (fun u : ℝ =>
      ccm24CriticalMellinLogProfileChainDeriv f u +
        ((-1 / 2 : ℝ) * Real.exp (-u / 2)) • f (Real.exp (-u)))
      (ccm24CriticalMellinLogProfileSecondDerivFormula f ξ) ξ
    exact hasDerivAt_ccm24CriticalMellinLogProfileFirstDeriv_formula f ξ
  · exact integrable_ccm24CriticalMellinLogProfile f
  · exact integrable_ccm24CriticalMellinLogProfileFirstDerivFormula f
  · exact integrable_ccm24CriticalMellinLogProfileSecondDerivFormula f

end Dev
end ConnesWeilRH
