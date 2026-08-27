/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20TranslateInvariance

/-!
# Uniform displacement bound for the CC20 correlation slices

Second stage of the Lemma-3 engine of arXiv:2006.13771 toward paper
equation (121).  The landed slice brick
`C1CC20CorrBridge.abs_corrInnerSlice_le` bounds the correlation slice by a
constant that still depends on the displacement through the mass of the
translated factor; here the real-integral shift twin removes that
dependence:

    ‖corrInnerSlice η ξ v‖ ≤ mass(η)^{1/2} · mass(ξ)^{1/2}   for ALL v,

with `mass(f) := ∫ ‖f x‖² dx` computed at zero displacement.

Ingredients, all verified against mathlib v4.30 by compiler probes:

`map_add_right_eq_self` (root namespace) — Lebesgue measure is invariant under
  right-addition (`IsAddRightInvariant` class instance);
* `integral_map` — Bochner integrals pull back along measurable maps;
* `quasiMeasurePreserving_add_right` +
  `AEStronglyMeasurable.comp_quasiMeasurePreserving` — strong
  measurability transports along translations;
* `AEStronglyMeasurable.norm`, `.pow` — closure under pointwise
  squared-norm constructions.

The remaining L2b step — folding the uniform bound against an `L¹`
weight into the full pairing domination — additionally needs the
strong measurability of the slice map `v ↦ corrInnerSlice η ξ v`; that
is contracted separately (doc 1043 §6n/L2b) and consumes
`QuasiMeasurePreserving.preimage_ae_eq` for the representative change.
No RH-level sign or coverage claim is made here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20UniformSlice

open MeasureTheory
open C1CC20CorrBridge C1CC20TranslateInvariance

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Real Bochner shift twin: integrating against Lebesgue measure ignores a
common additive shift in the argument. -/
theorem integral_shift {φ : ℝ → F} (hφ : AEStronglyMeasurable φ volume)
    (w : ℝ) :
    (∫ x : ℝ, φ (x + w)) = ∫ x : ℝ, φ x := by
  have hmeas : Measurable (fun x : ℝ => x + w) := by measurability
  have hmap : Measure.map (fun x : ℝ => x + w) volume = volume :=
    map_add_right_eq_self volume w
  -- The lemma wants the integrand measurable under the PUSHED measure;
  -- rewrite the pushforward onto `volume` first.
  have hrep : AEStronglyMeasurable φ
      (Measure.map (fun x : ℝ => x + w) volume) := by
    rw [hmap]
    exact hφ
  calc (∫ x : ℝ, φ (x + w))
      = ∫ y : ℝ, φ y ∂(Measure.map (fun x : ℝ => x + w) volume) :=
        Eq.symm (integral_map hmeas.aemeasurable hrep)
    _ = ∫ x : ℝ, φ x := by rw [hmap]

/-- The preimage of a null set under right-addition is null: the
combinatorial core of transporting a.e.-statements along shifts. -/
theorem measure_preimage_add_right_null {s : Set ℝ}
    (hs : MeasurableSet s) (hnull : volume s = 0) (w : ℝ) :
    volume ((fun x : ℝ => x + w) ⁻¹' s) = 0 := by
  have hmeas : Measurable (fun x : ℝ => x + w) := by measurability
  rw [← Measure.map_apply hmeas hs, map_add_right_eq_self volume w]
  exact hnull

/-- The pointwise squared norm of a translated MemLp function stays strongly
measurable: `.norm.pow` handles the pointwise construction, the translate
rides the quasi measure preserving map, and `simpa` normalizes the function
power/composition shapes onto plain lambdas. -/
theorem aestronglyMeasurable_norm_sq_shift {ξ : ℝ → ℂ}
    (hξ : MemLp ξ (ENNReal.ofReal 2)) (w : ℝ) :
    AEStronglyMeasurable (fun x => ‖ξ (x + w)‖ ^ (2 : ℝ)) volume := by
  have hb := (hξ.1.norm.pow 2).comp_quasiMeasurePreserving
    (quasiMeasurePreserving_add_right volume w)
  simpa using hb

/-- The REAL squared-norm mass is translation invariant — the concrete twin
the slice bound folds against. -/
theorem mass_shift_real {ξ : ℝ → ℂ}
    (_hξ : MemLp ξ (ENNReal.ofReal 2)) (w : ℝ) :
    (∫ x : ℝ, ‖ξ (x + w)‖ ^ (2 : ℝ)) = ∫ x : ℝ, ‖ξ x‖ ^ (2 : ℝ) := by
  have hval := integral_shift (_hξ.1.norm.pow 2) w
  simpa using hval

/-- Uniform Cauchy--Schwarz on displacement slices: the slice bound of
`C1CC20CorrBridge.abs_corrInnerSlice_le` with the translated factor's mass
pinned back to zero displacement — the constant is now DISPLACEMENT-FREE,
exactly the shape paper equation (121) folds over an `L¹` weight. -/
theorem abs_corrInnerSlice_uniform {η ξ : ℝ → ℂ}
    (heta : MemLp η (ENNReal.ofReal 2)) (hxi : MemLp ξ (ENNReal.ofReal 2))
    (v : ℝ) :
    ‖corrInnerSlice η ξ v‖ ≤
      (∫ x : ℝ, ‖η x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) *
        (∫ x : ℝ, ‖ξ x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
  refine (abs_corrInnerSlice_le heta (fun w => memLp_shift hxi w) v).trans ?_
  rw [mass_shift_real hxi v]

end C1CC20UniformSlice
end Source
end ConnesWeilRH
