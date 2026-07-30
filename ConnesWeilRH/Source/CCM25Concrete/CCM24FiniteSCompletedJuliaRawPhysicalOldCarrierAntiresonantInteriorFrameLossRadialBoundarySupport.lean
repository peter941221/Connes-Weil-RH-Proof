/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundarySplit

/-!
# Support and norm readout for the radial boundary channel

Proof 674 promotes the finite-window radial crossing readout from the actual
new-frame column to every input in the genuine upper radial support.  It then
specializes the result to the actual suffix Sonin projection `P_S`.

No graph-norm estimate is asserted.  The result only supplies the support and
contractive facts needed before taking absolute values in later signed trace
arguments.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AntiresonantFrameLossRadialBoundarySupport

open MeasureTheory Set
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open AntiresonantFrameLossCommutator
open AntiresonantFrameLossRadialBoundarySplit
open AntiresonantFrameLossRadialReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment

/-! ## Generic upper-radial input -/

/-- The positive translation of an upper-radial input leaves the support only
through the literal interval `[log(lambda)-log(p), log(lambda))`. -/
theorem radialBoundaryCrossing_coeFn_of_radialSupport
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    {u : finiteSCarrier}
    (hu : u ∈ ccm24LogRadialSupportClosedSubspace lambda) :
    ((radialComplement lambda ∘L
        (cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap) u :
        ℝ → ℂ) =ᵐ[volume]
      (Set.Ico (Real.log lambda - Real.log p) (Real.log lambda)).indicator
        (fun t => u (t + Real.log p)) := by
  let shifted := cc20GlobalLogTranslation (Real.log p) u
  have huZero :=
    (mem_ccm24LogRadialSupportClosedSubspace_iff lambda u).1 hu
  have huZeroShift :=
    (measurePreserving_add_right volume (Real.log p)).quasiMeasurePreserving.ae
      huZero
  have htranslation := cc20GlobalLogTranslation_coeFn (Real.log p) u
  have hprojection := ccm24TranslatedHalfLineProjection_coeFn lambda shifted
  rw [← ccm24LogRadialSupportProjection_eq_translatedHalfLine] at hprojection
  have hprojection' :
      (radialSupportProjection lambda shifted : ℝ → ℂ) =ᵐ[volume]
        (Set.Ici (Real.log lambda)).indicator (fun t => shifted t) := by
    simpa only [radialSupportProjection] using hprojection
  have hsub := Lp.coeFn_sub shifted (radialSupportProjection lambda shifted)
  filter_upwards [htranslation, hprojection', hsub, huZeroShift] with t
      htranslationAt hprojectionAt hsubAt huZeroAt
  change (shifted - radialSupportProjection lambda shifted : finiteSCarrier) t =
    (Set.Ico (Real.log lambda - Real.log p) (Real.log lambda)).indicator
      (fun s => u (s + Real.log p)) t
  rw [hsubAt]
  simp only [Pi.sub_apply]
  rw [hprojectionAt, htranslationAt]
  by_cases hlow : Real.log lambda - Real.log p ≤ t
  · by_cases hupp : t < Real.log lambda
    · have hwindow : t ∈ Set.Ico (Real.log lambda - Real.log p)
          (Real.log lambda) := ⟨hlow, hupp⟩
      have houtside : t ∉ Set.Ici (Real.log lambda) := by
        exact not_le.mpr hupp
      rw [Set.indicator_of_mem hwindow, Set.indicator_of_notMem houtside,
        sub_zero]
    · have hupp' : Real.log lambda ≤ t := le_of_not_gt hupp
      have houtside : t ∉ Set.Ico (Real.log lambda - Real.log p)
          (Real.log lambda) := by
        intro ht
        exact hupp ht.2
      have hinside : t ∈ Set.Ici (Real.log lambda) := hupp'
      rw [Set.indicator_of_notMem houtside, Set.indicator_of_mem hinside,
        htranslationAt, sub_self]
  · have hbelow : t + Real.log p < Real.log lambda := by linarith
    have hzero := huZeroAt hbelow
    have hnot : t ∉ Set.Ico (Real.log lambda - Real.log p)
        (Real.log lambda) := by
      simp only [Set.mem_Ico, not_and_or]
      exact Or.inl hlow
    have htlt : t < Real.log lambda := by
      have hpLog : 0 ≤ Real.log p :=
        Real.log_nonneg (by exact_mod_cast p.property.le)
      linarith
    have houtside : t ∉ Set.Ici (Real.log lambda) := by
      exact not_le.mpr htlt
    rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem houtside,
      hzero, sub_zero]

/-! ## Contractive norm readout -/

/-- The radial boundary crossing is contractive on every upper-radial input. -/
theorem norm_radialBoundaryCrossing_apply_le
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (u : finiteSCarrier) :
    ‖(radialComplement lambda)
        ((cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap u)‖ ≤
      ‖u‖ := by
  let complement := ContinuousLinearMap.id ℂ finiteSCarrier -
    radialSupportProjection lambda
  have hcomplement : IsStarProjection complement := by
    simpa only [complement] using
      (radialSupportProjection_isStarProjection lambda).one_sub
  calc
    ‖(radialComplement lambda)
        ((cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap u)‖ ≤
        ‖complement‖ *
          ‖(cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap u‖ := by
      exact complement.le_opNorm _
    _ ≤ 1 *
          ‖(cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap u‖ := by
      exact mul_le_mul_of_nonneg_right
        (IsStarProjection.norm_le complement hcomplement) (norm_nonneg _)
    _ = ‖u‖ := by
      simpa only [one_mul] using
        (norm_cc20GlobalLogTranslation (Real.log p) u)

/-! ## Actual suffix Sonin specialization -/

/-- The boundary channel from the actual suffix Sonin projection has the same
finite-window pointwise readout. -/
theorem radialSoninBoundaryCrossing_coeFn
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (v : finiteSCarrier) :
    (radialSoninBoundaryCrossing p S v : ℝ → ℂ) =ᵐ[volume]
      (Set.Ico (Real.log (unitSoninScale : ℝ) - Real.log p)
        (Real.log (unitSoninScale : ℝ))).indicator
        (fun t => newSuffixRangeProjection unitSoninScale S v
          (t + Real.log p)) := by
  have hfixed := DFunLike.congr_fun
    (radialSupportProjection_comp_newSuffixRangeProjection
      unitSoninScale S) v
  have hu :
      newSuffixRangeProjection unitSoninScale S v ∈
        ccm24LogRadialSupportClosedSubspace unitSoninScale := by
    apply (ccm24LogRadialSupportProjection_eq_self_iff unitSoninScale _).1
    simpa only [radialSupportProjection, ContinuousLinearMap.comp_apply] using
      hfixed
  simpa only [radialSoninBoundaryCrossing, ContinuousLinearMap.comp_apply] using
    (radialBoundaryCrossing_coeFn_of_radialSupport unitSoninScale p
      (u := newSuffixRangeProjection unitSoninScale S v) hu)

/-- The actual suffix boundary channel is bounded by the projected input. -/
theorem norm_radialSoninBoundaryCrossing_apply_le_projection
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (v : finiteSCarrier) :
    ‖radialSoninBoundaryCrossing p S v‖ ≤
      ‖newSuffixRangeProjection unitSoninScale S v‖ := by
  simpa only [radialSoninBoundaryCrossing, ContinuousLinearMap.comp_apply] using
    (norm_radialBoundaryCrossing_apply_le unitSoninScale p
      (newSuffixRangeProjection unitSoninScale S v))

/-- Contractivity of the suffix Sonin projection gives an ambient norm bound
for the actual boundary channel. -/
theorem norm_radialSoninBoundaryCrossing_apply_le
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (v : finiteSCarrier) :
    ‖radialSoninBoundaryCrossing p S v‖ ≤ ‖v‖ := by
  calc
    ‖radialSoninBoundaryCrossing p S v‖ ≤
        ‖newSuffixRangeProjection unitSoninScale S v‖ :=
      norm_radialSoninBoundaryCrossing_apply_le_projection p S v
    _ ≤ ‖v‖ := norm_newSuffixRangeProjection_apply_le unitSoninScale S v

end AntiresonantFrameLossRadialBoundarySupport
end CCM25Concrete
end Source
end ConnesWeilRH
