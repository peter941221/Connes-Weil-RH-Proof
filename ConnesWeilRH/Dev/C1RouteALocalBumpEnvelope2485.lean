import ConnesWeilRH.Dev.C1RouteABumpDerivativeLadder

/-  2485: local multiplicative envelope for one bump derivative.

The cell proof may bound the three factors separately on a closed subinterval:
the bump numerator, the inverse-deficit power, and the exponential.  This
lemma combines those bounds exactly; it does not supply any numerical values
for them. -/

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false
set_option maxRecDepth 32768

theorem scaledBumpJet2350_abs_le_of_local_bounds2485
    (order : ℕ)
    {radius position : ℝ} (hradius : 0 < radius) (hinside : |position| < radius)
    (numeratorBound inversePowerBound exponentialBound : ℝ)
    (hnum : |bumpNumerator2350 order (position / radius)| ≤ numeratorBound)
    (hinverse : (bumpDeficit2350 (position / radius))⁻¹ ^ (2 * order) ≤
      inversePowerBound)
    (hexponential : Real.exp (-30 / bumpDeficit2350 (position / radius)) ≤
      exponentialBound)
    (hinverse_nonneg : 0 ≤ inversePowerBound)
    (hexponential_nonneg : 0 ≤ exponentialBound) :
    |scaledBumpJet2350 order radius position| ≤
      exponentialBound * inversePowerBound * numeratorBound / radius ^ order := by
  have hdeficit : 0 < bumpDeficit2350 (position / radius) := by
    exact familyDeficit2345_pos hradius hinside
  have hinverse_nonneg' :
      0 ≤ (bumpDeficit2350 (position / radius))⁻¹ ^ (2 * order) := by
    positivity
  have hexponential_nonneg' :
      0 ≤ Real.exp (-30 / bumpDeficit2350 (position / radius)) := by
    positivity
  have hfirst := mul_le_mul hexponential hinverse
    hinverse_nonneg' hexponential_nonneg
  have hsecond := mul_le_mul hfirst hnum
    (abs_nonneg _) (mul_nonneg hexponential_nonneg hinverse_nonneg)
  have hjet :
      |bumpJet2350 order (bumpNumerator2350 order) (position / radius)| ≤
        exponentialBound * inversePowerBound * numeratorBound := by
    rw [bumpJet2350, abs_mul, abs_mul,
      abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hdeficit.le) _)]
    exact hsecond
  rw [scaledBumpJet2350, abs_div, abs_of_pos (pow_pos hradius order)]
  exact div_le_div_of_nonneg_right hjet (pow_nonneg hradius.le _)

end ConnesWeilRH.Dev
