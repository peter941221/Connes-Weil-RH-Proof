/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20WindowedDisplacementReadback
import ConnesWeilRH.Dev.C1CC20ProductIntegrability

/-!
# CC20 square-window pairing readback

The equation-(121) engine controls pairings of a raw displacement kernel.  A
CC20 endpoint kernel is square-windowed, so both the input and output must be
restricted before that engine applies.  This leaf proves the resulting exact
pairing relation and its automatic L1 x L2 x L2 estimate:

    <eta, K_I xi> = <E_I eta, K E_I xi>.

Here `E_I` denotes restriction to the window followed by zero extension to the
ambient line.  No finite-rank approximant or numerical profile certificate is
introduced.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20WindowedPairingReadback

open MeasureTheory
open C1CC20CorrBridge C1CC20DisplacementKernel C1CC20DisplacementReadback
  C1CC20LpOperator C1CC20ProductIntegrability C1CC20RawKernelMass
  C1CC20WindowedDisplacementReadback

/-- Zero extension to a measurable CC20 window preserves `MemLp`. -/
theorem memLp_cc20WindowZeroExtend
    {p : ENNReal} {f : ℝ -> ℂ} (r : ℝ) (hf : MemLp f p volume) :
    MemLp (cc20WindowZeroExtend r f) p volume := by
  unfold cc20WindowZeroExtend
  exact MemLp.indicator (measurableSet_cc20Window r) hf

/-- Pairing a square-window displacement action is exactly the raw pairing of
the two zero-extended factors. -/
theorem pairing_applyKernel_windowedDisplacementKernel_eq_zeroExtendRaw
    (a eta xi : ℝ -> ℂ) (r : ℝ) :
    (∫ x : ℝ, eta x * applyKernel (windowedDisplacementKernel a r) xi x) =
      ∫ x : ℝ, cc20WindowZeroExtend r eta x *
        applyKernel (displacementKernel a) (cc20WindowZeroExtend r xi) x := by
  apply integral_congr_ae
  filter_upwards with x
  rw [applyKernel_windowedDisplacementKernel_eq_zeroExtend]
  unfold cc20WindowZeroExtend
  by_cases hx : x ∈ cc20Window r <;> simp [hx]

/-- The exact equation-(121) readback for a square-window displacement kernel.
The caller retains the explicit Fubini premise for the two zero-extended
factors. -/
theorem pairing_applyKernel_windowedDisplacementKernel_eq_weightedCorrFold
    (a eta xi : ℝ -> ℂ) (r : ℝ)
    (hintegrable : Integrable
      (Function.uncurry (displacementCorrelationIntegrand a
        (cc20WindowZeroExtend r eta) (cc20WindowZeroExtend r xi)))
      (volume.prod volume)) :
    (∫ x : ℝ, eta x * applyKernel (windowedDisplacementKernel a r) xi x) =
      ∫ v : ℝ, a v *
        corrInnerSlice (cc20WindowZeroExtend r eta)
          (cc20WindowZeroExtend r xi) v := by
  calc
    (∫ x : ℝ, eta x * applyKernel (windowedDisplacementKernel a r) xi x) =
        ∫ x : ℝ, cc20WindowZeroExtend r eta x *
          applyKernel (displacementKernel a) (cc20WindowZeroExtend r xi) x :=
      pairing_applyKernel_windowedDisplacementKernel_eq_zeroExtendRaw a eta xi r
    _ = ∫ v : ℝ, a v *
        corrInnerSlice (cc20WindowZeroExtend r eta)
          (cc20WindowZeroExtend r xi) v :=
      pairing_applyKernel_displacementKernel_eq_weightedCorrFold a
        (cc20WindowZeroExtend r eta) (cc20WindowZeroExtend r xi) hintegrable

/-- Equation-(121) bounds a square-window displacement-kernel pairing with no
remaining Fubini premise once the profile is L1 and both factors are L2. -/
theorem norm_pairing_applyKernel_windowedDisplacementKernel_le_of_l1Weight
    {a eta xi : ℝ -> ℂ} (r : ℝ)
    (ha : AEStronglyMeasurable a volume)
    (haint : Integrable (fun v => ‖a v‖) volume)
    (heta : MemLp eta (ENNReal.ofReal 2))
    (hxi : MemLp xi (ENNReal.ofReal 2)) :
    ‖∫ x : ℝ, eta x * applyKernel (windowedDisplacementKernel a r) xi x‖ ≤
      (∫ x : ℝ, ‖cc20WindowZeroExtend r eta x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) *
        (∫ x : ℝ, ‖cc20WindowZeroExtend r xi x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) *
          ∫ v : ℝ, ‖a v‖ := by
  rw [pairing_applyKernel_windowedDisplacementKernel_eq_zeroExtendRaw]
  exact norm_pairing_applyKernel_displacementKernel_le_of_l1Weight ha haint
    (memLp_cc20WindowZeroExtend r heta)
    (memLp_cc20WindowZeroExtend r hxi)

/-- Concrete CC20 endpoint specialization of the automatic square-window
pairing bound. -/
theorem norm_pairing_applyKernel_endpointKernelOnSquare_le_of_l1Weight
    {eta xi : ℝ -> ℂ} (data : CC20Concrete.CC20EndpointSpectralData) (r : ℝ)
    (ha : AEStronglyMeasurable (endpointDisplacementProfile data) volume)
    (haint : Integrable (fun v => ‖endpointDisplacementProfile data v‖) volume)
    (heta : MemLp eta (ENNReal.ofReal 2))
    (hxi : MemLp xi (ENNReal.ofReal 2)) :
    ‖∫ x : ℝ, eta x * applyKernel (endpointKernelOnSquare data r) xi x‖ ≤
      (∫ x : ℝ, ‖cc20WindowZeroExtend r eta x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) *
        (∫ x : ℝ, ‖cc20WindowZeroExtend r xi x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) *
          ∫ v : ℝ, ‖endpointDisplacementProfile data v‖ := by
  rw [endpointKernelOnSquare_eq_windowedDisplacementKernel]
  exact norm_pairing_applyKernel_windowedDisplacementKernel_le_of_l1Weight r
    ha haint heta hxi

end C1CC20WindowedPairingReadback
end Source
end ConnesWeilRH
