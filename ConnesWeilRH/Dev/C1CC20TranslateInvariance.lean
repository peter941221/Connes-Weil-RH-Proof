/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20CorrBridge

/-!
# Translation invariance pack for the correlation bridge

Discharges the shift slot of `C1CC20CorrBridge.abs_corrInnerSlice_le`:
on Lebesgue space, translating the argument preserves `MemLp 2`.

Ingredients (all mathlib-native, signatures confirmed against v4.30):

* `quasiMeasurePreserving_add_right μ g` — right-addition is a quasi
  measure preserving self-map (`IsAddLeftInvariant` side);
* `AEStronglyMeasurable.comp_quasiMeasurePreserving`;
* `lintegral_add_right_eq_self f g : ∫⁻ x, f (x + g) = ∫⁻ x, f x` — the
  `∫⁻` mass is exactly invariant; feeding the *unshifted* base produces
  the shifted-vs-plain identity we need;
* the `eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top` expansion used by
  `C1CC20RawKernelMass.memLp_…_of_mass_lt_top`, here also read backwards
  (`ltTop_of_memLp`) so finiteness can be *recovered* from a `MemLp`
  hypothesis rather than assumed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20TranslateInvariance

open MeasureTheory

/-- The shifted squared-`enorm` mass equals the original one. -/
theorem lintegral_enorm_sq_shift {ξ : ℝ → ℂ}
    (_hx : MemLp ξ (ENNReal.ofReal 2)) (w : ℝ) :
    (∫⁻ x : ℝ, ‖ξ (x + w)‖ₑ ^ (2 : ℝ))
      = (∫⁻ x : ℝ, ‖ξ x‖ₑ ^ (2 : ℝ)) :=
  lintegral_add_right_eq_self (fun x => ‖ξ x‖ₑ ^ (2 : ℝ)) w

/-- Recover plain squared-`enorm` mass finiteness from `MemLp 2`:
the pointwise companion of the expansion used in
`C1CC20RawKernelMass.memLp_endpointKernelOnSquare_of_mass_lt_top`,
read in the opposite direction. -/
theorem ltTop_of_memLp {ξ : ℝ → ℂ} (hξ : MemLp ξ (ENNReal.ofReal 2)) :
    (∫⁻ x : ℝ, ‖ξ x‖ₑ ^ (2 : ℝ)) < ⊤ := by
  have hpz : ENNReal.ofReal 2 ≠ 0 := (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  have hpt : ENNReal.ofReal 2 ≠ ⊤ := ENNReal.ofReal_ne_top
  -- Read the expansion *forwards* so the statement comes out in the lemma's
  -- own shape (exponent written as `(ENNReal.ofReal 2).toReal`); rewriting
  -- backwards onto a literal `2` misses the pattern.
  have hexpl := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hpz hpt).mp hξ.2
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)] at hexpl
  exact hexpl

/-- Translating the input preserves `MemLp 2`: strong measurability is
transported along the quasi measure preserving right-addition, and
finiteness comes from the shifted-mass invariance above. -/
theorem memLp_shift {ξ : ℝ → ℂ} (hξ : MemLp ξ (ENNReal.ofReal 2)) (w : ℝ) :
    MemLp (fun x => ξ (x + w)) (ENNReal.ofReal 2) := by
  have haes : AEStronglyMeasurable (fun x => ξ (x + w)) volume :=
    hξ.1.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_add_right volume w)
  refine ⟨haes, ?_⟩
  have hpz : ENNReal.ofReal 2 ≠ 0 := (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  have hpt : ENNReal.ofReal 2 ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hpz hpt]
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
  have hmass : (∫⁻ x : ℝ, ‖ξ (x + w)‖ₑ ^ (2 : ℝ)) < ⊤ := by
    rw [lintegral_enorm_sq_shift hξ w]
    exact ltTop_of_memLp hξ
  simpa using hmass

end C1CC20TranslateInvariance
end Source
end ConnesWeilRH
