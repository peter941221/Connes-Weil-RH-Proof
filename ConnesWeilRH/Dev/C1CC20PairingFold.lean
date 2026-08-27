/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20UniformSlice

/-!
# Pairing fold over an L¹ weight — paper equation (121)

Final stage of the Lemma-3 engine of arXiv:2006.13771, iterated form:

    ‖∫ v, a(v) • corrInnerSlice η ξ v‖ ≤ mass(η)^{1/2} · mass(ξ)^{1/2}
                                         · ∫ ‖a v‖ dv,

with `corrInnerSlice` from `C1CC20CorrBridge`.  Slice-map measurability is
discharged inline: MemLp's definitional form is an existential, so Borel
representatives come free via `obtain`; the joint function rides
`StronglyMeasurable.comp_measurable` + `.mul`; partial integration uses
`StronglyMeasurable.integral_prod_right`; per-displacement value equality
rides `C1CC20UniformSlice.eventuallyEq_comp_add_right`.  Domination closes
with `Integrable.mono`.

No RH-level sign or coverage claim is made here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20PairingFold

open MeasureTheory
open C1CC20CorrBridge C1CC20TranslateInvariance C1CC20UniformSlice

/-- The displacement-slice map is strongly measurable: representatives
from the `MemLp` existentials assemble the joint function, partial
integration keeps measurability, and a per-`v` change of integrands —
riding the shift transport of a.e.-equalities — identifies it with the
original correlation slices. -/
theorem aestronglyMeasurable_corrInnerSlice {η ξ : ℝ → ℂ}
    (heta : MemLp η (ENNReal.ofReal 2))
    (hxi : MemLp ξ (ENNReal.ofReal 2)) :
    AEStronglyMeasurable (fun v => corrInnerSlice η ξ v) volume := by
  obtain ⟨eη, hSMη, haeη⟩ := heta.1
  obtain ⟨eξ, hSMξ, haeξ⟩ := hxi.1
  -- Joint strong measurability on ℝ×ℝ (coordinates arranged so that the
  -- function IS the uncurry of `fun v x => eη x * eξ (x + v)`).
  have hA : StronglyMeasurable (fun p : ℝ × ℝ => eη p.2) :=
    hSMη.comp_measurable (by measurability)
  have hB : StronglyMeasurable (fun p : ℝ × ℝ => eξ (p.2 + p.1)) :=
    hSMξ.comp_measurable (by measurability)
  have hJoint : StronglyMeasurable
      (Function.uncurry fun v x => eη x * eξ (x + v)) :=
    hA.mul hB
  -- Partial integration over the displacement-free coordinate.
  have hvsm : StronglyMeasurable
      (fun v => ∫ y, (fun x => eη x * eξ (x + v)) y ∂volume) :=
    StronglyMeasurable.integral_prod_right hJoint
  -- Per-displacement value equality between original and representative
  -- slices, via the a.e.-transport along right-addition.
  have key : ∀ v : ℝ,
      corrInnerSlice η ξ v = ∫ y, (fun x => eη x * eξ (x + v)) y ∂volume := by
    intro v
    rw [corrInnerSlice]
    apply integral_congr_ae
    filter_upwards [haeη, eventuallyEq_comp_add_right haeξ v] with x hx hx'
    rw [hx, hx']
  rw [(funext key : (fun v => corrInnerSlice η ξ v) =
    fun v => ∫ y, (fun x => eη x * eξ (x + v)) y ∂volume)]
  exact hvsm.aestronglyMeasurable

/-- Paper equation (121), iterated form: folding the uniform displacement
bound against an `L¹` weight dominates the pairing by the product of the
two squared-norm half-masses and the `L¹` mass of the weight. -/
theorem abs_corrWeightedFold_le {η ξ : ℝ → ℂ}
    (heta : MemLp η (ENNReal.ofReal 2))
    (hxi : MemLp ξ (ENNReal.ofReal 2))
    {a : ℝ → ℂ} (ha : AEStronglyMeasurable a volume)
    (haint : Integrable (fun v => ‖a v‖) volume) :
    ‖∫ v : ℝ, a v * corrInnerSlice η ξ v‖ ≤
      (∫ x : ℝ, ‖η x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) *
        (∫ x : ℝ, ‖ξ x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) * ∫ v : ℝ, ‖a v‖ := by
  classical
  set K : ℝ := (∫ x : ℝ, ‖η x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) *
    (∫ x : ℝ, ‖ξ x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) with hKdef
  have hc := aestronglyMeasurable_corrInnerSlice heta hxi
  have hP : AEStronglyMeasurable
      (fun v => a v * corrInnerSlice η ξ v) volume :=
    (ha.mul hc).congr (by
      filter_upwards with v
      rfl)
  -- Pointwise domination of the folded pairing by the scaled weight.
  have hmassη : 0 ≤ ∫ x : ℝ, ‖η x‖ ^ (2 : ℝ) :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hmassξ : 0 ≤ ∫ x : ℝ, ‖ξ x‖ ^ (2 : ℝ) :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hKnn : 0 ≤ K :=
    mul_nonneg (Real.rpow_nonneg hmassη _) (Real.rpow_nonneg hmassξ _)
  -- The domination core, stated POINTWISE (holds everywhere, no a.e.
  -- needed): the folded pairing never exceeds the scaled weight.
  have hspoint : ∀ v : ℝ,
      ‖a v * corrInnerSlice η ξ v‖ ≤ K * ‖a v‖ := by
    intro v
    rw [norm_mul]
    have hub := abs_corrInnerSlice_uniform heta hxi v
    nlinarith [hub, norm_nonneg (a v)]
  have hgint : Integrable (fun v => K * ‖a v‖) volume :=
    haint.const_mul K
  -- Integrable.mono wants the bound against the norm-wrapped real weight;
  -- hKnn unwraps it to the same pointwise statement.
  have hPint : Integrable (fun v => a v * corrInnerSlice η ξ v) volume := by
    refine hgint.mono hP ?_
    filter_upwards with v
    have hv := hspoint v
    change ‖a v * corrInnerSlice η ξ v‖ ≤ ‖(fun w => K * ‖a w‖) v‖
    rwa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hKnn (norm_nonneg _))]
  have hqint : Integrable (fun v => ‖a v * corrInnerSlice η ξ v‖) volume :=
    hPint.norm
  calc ‖∫ v : ℝ, a v * corrInnerSlice η ξ v‖
      ≤ ∫ v : ℝ, ‖a v * corrInnerSlice η ξ v‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ v : ℝ, K * ‖a v‖ :=
        MeasureTheory.integral_mono hqint hgint hspoint
    _ = K * ∫ v : ℝ, ‖a v‖ := MeasureTheory.integral_const_mul K _

end C1CC20PairingFold
end Source
end ConnesWeilRH
