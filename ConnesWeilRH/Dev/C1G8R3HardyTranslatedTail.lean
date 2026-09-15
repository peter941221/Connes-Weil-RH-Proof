/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3LeakageDoubledShift
import ConnesWeilRH.Dev.C1SemilocalHardyTitchmarshUnitarityReduction

/-!
# Translated Hardy tails for the R3 leakage channel

On the common global-log L2 carrier, a translated positive-half-line
projection is exactly the translated tail of the original vector.  The tail
has vanishing L2 norm.  Hardy--Titchmarsh reverses translations, so the source
Fourier-support projection vanishes in norm along the opposite translated
orbit.  This is an input-direction decay statement; it does not assert an
operator trace estimate or a Weil sign.
-/

namespace ConnesWeilRH
namespace Dev

open Filter
open MeasureTheory
open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment
open Source.C1SemilocalHardyTitchmarshUnitarityReduction
open scoped Topology

private noncomputable def positiveHalfLineTailFunction
    (u : cc20GlobalLogCrossingL2) (n : ℕ) : ℝ → ENNReal :=
  (Set.Ici (n : ℝ)).indicator
    (fun x => ‖(u : ℝ → ℂ) x‖ₑ ^ (2 : ℝ))

private noncomputable def positiveHalfLineTail
    (u : cc20GlobalLogCrossingL2) (n : ℕ) : cc20GlobalLogCrossingL2 :=
  ((memLp_indicator_iff_restrict measurableSet_Ici).2
      ((Lp.memLp u).restrict (Set.Ici (n : ℝ)))).toLp
    ((Set.Ici (n : ℝ)).indicator (fun x => (u : ℝ → ℂ) x))

private theorem positiveHalfLineTail_coeFn
    (u : cc20GlobalLogCrossingL2) (n : ℕ) :
    (positiveHalfLineTail u n : ℝ → ℂ) =ᵐ[volume]
      (Set.Ici (n : ℝ)).indicator (fun x => (u : ℝ → ℂ) x) := by
  exact MemLp.coeFn_toLp _

private theorem tendsto_positiveHalfLineTail_lintegral
    (u : cc20GlobalLogCrossingL2) :
    Tendsto
      (fun n => ∫⁻ x, positiveHalfLineTailFunction u n x
        ∂(volume : Measure ℝ)) atTop (𝓝 0) := by
  have hmeas (n : ℕ) :
      AEMeasurable (positiveHalfLineTailFunction u n) (volume : Measure ℝ) := by
    exact ((Lp.memLp u).1.enorm.pow_const (2 : ℝ)).indicator
      measurableSet_Ici
  have htotal_lt_top :=
    lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (μ := (volume : Measure ℝ)) (p := (2 : ENNReal))
      (f := (u : ℝ → ℂ)) two_ne_zero ENNReal.ofNat_ne_top
      (Lp.eLpNorm_lt_top u)
  have hzero_le_total :
      (∫⁻ x, positiveHalfLineTailFunction u 0 x
        ∂(volume : Measure ℝ)) ≤
        (∫⁻ x, ‖(u : ℝ → ℂ) x‖ₑ ^ (2 : ℝ)
          ∂(volume : Measure ℝ)) := by
    apply lintegral_mono
    intro x
    simp only [positiveHalfLineTailFunction, Set.indicator_apply]
    split_ifs <;> simp
  have hzero_ne_top := (hzero_le_total.trans_lt htotal_lt_top).ne
  have hanti : ∀ x, Antitone
      (fun n => positiveHalfLineTailFunction u n x) := by
    intro x m n hmn
    have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hsubset : Set.Ici (n : ℝ) ⊆ Set.Ici (m : ℝ) :=
      Set.Ici_subset_Ici.mpr hmnR
    by_cases hm : x ∈ Set.Ici (m : ℝ)
    · by_cases hn : x ∈ Set.Ici (n : ℝ)
      · simp [positiveHalfLineTailFunction, hm, hn]
      · simp [positiveHalfLineTailFunction, hm, hn]
    · have hn : x ∉ Set.Ici (n : ℝ) := by
        intro hx
        exact hm (hsubset hx)
      simp [positiveHalfLineTailFunction, hm, hn]
  have heventually (x : ℝ) :
      ∀ᶠ n : ℕ in atTop, x ∉ Set.Ici (n : ℝ) := by
    have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    filter_upwards [hn.eventually (eventually_gt_atTop x)] with n hnx
    exact not_le_of_gt hnx
  have hpoint (x : ℝ) :
      Tendsto (fun n => positiveHalfLineTailFunction u n x)
        atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [heventually x] with n hn
    simp [positiveHalfLineTailFunction, hn]
  have hlintegral := lintegral_tendsto_of_tendsto_of_antitone
    hmeas (ae_of_all _ hanti) hzero_ne_top (ae_of_all _ hpoint)
  simpa [positiveHalfLineTailFunction] using hlintegral

private theorem tendsto_positiveHalfLineTail_eLpNorm
    (u : cc20GlobalLogCrossingL2) :
    Tendsto
      (fun n => eLpNorm (positiveHalfLineTail u n : ℝ → ℂ)
        (2 : ENNReal) (volume : Measure ℝ)) atTop (𝓝 0) := by
  have hlin := tendsto_positiveHalfLineTail_lintegral u
  have hpow : Tendsto
      (fun n =>
        (∫⁻ x, positiveHalfLineTailFunction u n x
          ∂(volume : Measure ℝ)) ^ (1 / 2 : ℝ))
      atTop (𝓝 ((0 : ENNReal) ^ (1 / 2 : ℝ))) :=
    (ENNReal.continuous_rpow_const.tendsto 0).comp hlin
  have hnorm (n : ℕ) :
      eLpNorm (positiveHalfLineTail u n : ℝ → ℂ)
          (2 : ENNReal) (volume : Measure ℝ) =
        (∫⁻ x, positiveHalfLineTailFunction u n x
          ∂(volume : Measure ℝ)) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero
      ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [positiveHalfLineTail_coeFn u n] with x hx
    rw [hx]
    by_cases hx' : x ∈ Set.Ici (n : ℝ)
    · simp [positiveHalfLineTailFunction, Set.indicator, hx']
    · simp [positiveHalfLineTailFunction, Set.indicator, hx']
  simpa [hnorm] using hpow

private theorem tendsto_positiveHalfLineTail
    (u : cc20GlobalLogCrossingL2) :
    Tendsto (fun n => positiveHalfLineTail u n) atTop (𝓝 0) := by
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  have herror : Tendsto
      (fun n => eLpNorm
        ((positiveHalfLineTail u n : ℝ → ℂ) - fun _ : ℝ => (0 : ℂ))
        (2 : ENNReal) (volume : Measure ℝ)) atTop (𝓝 0) := by
    have hfun (n : ℕ) :
        ((positiveHalfLineTail u n : ℝ → ℂ) - fun _ : ℝ => (0 : ℂ)) =
          (positiveHalfLineTail u n : ℝ → ℂ) := by
      funext x
      simp
    simpa only [hfun] using tendsto_positiveHalfLineTail_eLpNorm u
  have hzero : MemLp (fun _ : ℝ => (0 : ℂ)) (2 : ENNReal) volume := by
    exact MemLp.zero'
  simpa using
    (Lp.tendsto_Lp_of_tendsto_eLpNorm
      (fun _ : ℝ => (0 : ℂ)) hzero herror)

/-- Translating a vector left and retaining its positive half-line has norm
equal to the original vector's tail beyond the translation distance. -/
theorem cc20PositiveHalfLineProjection_globalLogTranslation_tendsto_zero
    (u : cc20GlobalLogCrossingL2) :
    Tendsto
      (fun n : ℕ => cc20PositiveHalfLineProjection
        (cc20GlobalLogTranslation (n : ℝ) u))
      atTop (𝓝 0) := by
  have hidentity (n : ℕ) :
      cc20PositiveHalfLineProjection
          (cc20GlobalLogTranslation (n : ℝ) u) =
        cc20GlobalLogTranslation (n : ℝ) (positiveHalfLineTail u n) := by
    rw [Lp.ext_iff]
    have hproj := cc20PositiveHalfLineProjection_coeFn
      (cc20GlobalLogTranslation (n : ℝ) u)
    have htrans := cc20GlobalLogTranslation_coeFn (n : ℝ) u
    have htail := positiveHalfLineTail_coeFn u n
    have htailShift :=
      (measurePreserving_add_right volume (n : ℝ)).quasiMeasurePreserving.ae_eq htail
    have hright := cc20GlobalLogTranslation_coeFn (n : ℝ)
      (positiveHalfLineTail u n)
    filter_upwards [hproj, htrans, htailShift, hright]
      with x hp ht htailShiftAt hr
    have htailShiftAt' :
        (positiveHalfLineTail u n : ℝ → ℂ) (x + n) =
          (Set.Ici (n : ℝ)).indicator
            (fun t => (u : ℝ → ℂ) t) (x + n) := by
      simpa only [Function.comp_apply] using htailShiftAt
    rw [hp, hr]
    change (Set.Ici (0 : ℝ)).indicator
        (fun t => (cc20GlobalLogTranslation (n : ℝ) u : ℝ → ℂ) t) x =
      (positiveHalfLineTail u n : ℝ → ℂ) (x + n)
    by_cases hx : x ∈ Set.Ici (0 : ℝ)
    · have hx' : x + (n : ℝ) ∈ Set.Ici (n : ℝ) := by
        change (n : ℝ) ≤ x + (n : ℝ)
        exact le_add_of_nonneg_left (by simpa using hx)
      simp only [Set.indicator_of_mem hx]
      rw [ht, htailShiftAt']
      simp [Set.indicator, hx']
    · have hx' : x + (n : ℝ) ∉ Set.Ici (n : ℝ) := by
        change ¬ (n : ℝ) ≤ x + (n : ℝ)
        intro h
        apply hx
        change 0 ≤ x
        linarith
      simp [Set.indicator, hx]
      rw [htailShiftAt']
      simp [Set.indicator, hx']
  have hnorm (n : ℕ) :
      ‖cc20PositiveHalfLineProjection
          (cc20GlobalLogTranslation (n : ℝ) u)‖ =
        ‖positiveHalfLineTail u n‖ := by
    rw [hidentity, norm_cc20GlobalLogTranslation]
  have htailnorm : Tendsto
      (fun n : ℕ => ‖positiveHalfLineTail u n‖) atTop (𝓝 0) :=
    by simpa only [Function.comp_apply, norm_zero] using
      (continuous_norm.tendsto 0).comp (tendsto_positiveHalfLineTail u)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [hnorm] using htailnorm

/-- A compactly supported vector translated sufficiently far to the right is
fixed by the positive half-line projection. -/
theorem cc20PositiveHalfLineProjection_globalLogTranslation_neg_eq_self_of_support
    (u : cc20GlobalLogCrossingL2) (a c : ℝ)
    (hsupp : Function.support (u : ℝ → ℂ) ⊆ Set.Icc a c)
    (n : ℕ) (hn : -a ≤ (n : ℝ)) :
    cc20PositiveHalfLineProjection
        (cc20GlobalLogTranslation (-(n : ℝ)) u) =
      cc20GlobalLogTranslation (-(n : ℝ)) u := by
  rw [Lp.ext_iff]
  have hproj := cc20PositiveHalfLineProjection_coeFn
    (cc20GlobalLogTranslation (-(n : ℝ)) u)
  have htrans := cc20GlobalLogTranslation_coeFn (-(n : ℝ)) u
  filter_upwards [hproj, htrans] with x hp ht
  rw [hp]
  by_cases hx : x ∈ Set.Ici (0 : ℝ)
  · have hx' : x ∈ cc20PositiveHalfLine := by
        simpa [cc20PositiveHalfLine] using hx
    rw [Set.indicator_of_mem hx']
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hzero : (u : ℝ → ℂ) (x - n) = 0 := by
      by_contra hne
      have hmem : x - (n : ℝ) ∈ Function.support (u : ℝ → ℂ) := hne
      have hbound := hsupp hmem
      have hlo := hbound.1
      change a ≤ x - (n : ℝ) at hlo
      linarith
    have hzero' : (u : ℝ → ℂ) (x + -(n : ℝ)) = 0 := by
      simpa only [sub_eq_add_neg] using hzero
    have hx' : x ∉ cc20PositiveHalfLine := by
      simpa [cc20PositiveHalfLine] using hx
    simp [Set.indicator, hx']
    rw [ht]
    exact hzero'.symm

/-- Along the right-translated orbit, the archimedean source Fourier-support
projection tends to zero in norm.  The Hardy transform reverses translation,
so this is precisely the positive-tail estimate above. -/
theorem sourceFourierSupportProjection_unit_globalLogTranslation_neg_tendsto_zero
    (u : finiteSCarrier) :
    Tendsto
      (fun n : ℕ => sourceFourierSupportProjection unitSoninScale
        (cc20GlobalLogTranslation (-(n : ℝ)) u))
      atTop (𝓝 0) := by
  have hhardy (n : ℕ) :
      archimedeanHardyTitchmarshOperator
          (cc20GlobalLogTranslation (-(n : ℝ)) u) =
        cc20GlobalLogTranslation (n : ℝ)
          (archimedeanHardyTitchmarshOperator u) := by
    simpa only [neg_neg] using
      archimedeanHardyTitchmarsh_globalLogTranslation
        (-(n : ℝ)) u
  have hproj (n : ℕ) :
      sourceFourierSupportProjection unitSoninScale
          (cc20GlobalLogTranslation (-(n : ℝ)) u) =
        archimedeanHardyTitchmarshOperator
          (cc20PositiveHalfLineProjection
            (cc20GlobalLogTranslation (n : ℝ)
              (archimedeanHardyTitchmarshOperator u))) := by
    have hradial :
        radialSupportProjection unitSoninScale =
          cc20PositiveHalfLineProjection := by
      exact radialSupportProjection_unit
    rw [sourceFourierSupportProjection_eq_hardyTitchmarsh_conjugation,
      hradial]
    simp only [ContinuousLinearMap.comp_apply, hhardy]
  have hnorm (n : ℕ) :
      ‖sourceFourierSupportProjection unitSoninScale
          (cc20GlobalLogTranslation (-(n : ℝ)) u)‖ =
        ‖cc20PositiveHalfLineProjection
          (cc20GlobalLogTranslation (n : ℝ)
            (archimedeanHardyTitchmarshOperator u))‖ := by
    rw [hproj]
    change ‖ccm24ArchimedeanHardyTitchmarsh
      (cc20PositiveHalfLineProjection
        (cc20GlobalLogTranslation (n : ℝ)
          (archimedeanHardyTitchmarshOperator u)))‖ = _
    exact ccm24ArchimedeanHardyTitchmarsh.norm_map _
  have htailnorm :=
    cc20PositiveHalfLineProjection_globalLogTranslation_tendsto_zero
      (archimedeanHardyTitchmarshOperator u)
  have hnorm_tendsto : Tendsto
      (fun n : ℕ =>
        ‖sourceFourierSupportProjection unitSoninScale
          (cc20GlobalLogTranslation (-(n : ℝ)) u)‖)
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, norm_zero, hnorm] using
      (continuous_norm.tendsto 0).comp htailnorm
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [hnorm] using hnorm_tendsto

end Dev
end ConnesWeilRH
