/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3StrongTracePairTransfer

/-!
# Strong limit of expanding output windows

The symmetric interval projections on the global logarithmic L2 carrier tend
strongly to the identity.  This is the analytic input needed to transport the
actual finite output window in the G8 leakage/source channel; it does not yet
identify or estimate the remaining G8 channels.
-/

namespace ConnesWeilRH
namespace Dev

open Filter
open MeasureTheory
open Source.CC20Concrete
open Source.CCM25Concrete.SelectedCrossingOperatorBridge
open scoped Topology

private noncomputable def symmetricWindowTail
    (u : cc20GlobalLogCrossingL2) (n : ℕ) : ℝ → ENNReal :=
  (Set.Icc (-(n : ℝ)) (n : ℝ))ᶜ.indicator
    (fun x => ‖(u : ℝ → ℂ) x‖ₑ ^ (2 : ℝ))

private theorem tendsto_symmetricWindowTail_lintegral
    (u : cc20GlobalLogCrossingL2) :
    Tendsto (fun n => ∫⁻ x, symmetricWindowTail u n x ∂(volume : Measure ℝ))
      atTop (𝓝 0) := by
  have hmeas (n : ℕ) :
    AEMeasurable (symmetricWindowTail u n) (volume : Measure ℝ) := by
    exact ((Lp.memLp u).1.enorm.pow_const (2 : ℝ)).indicator
      (measurableSet_Icc.compl)
  have htotal_lt_top :=
    lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (μ := (volume : Measure ℝ)) (p := (2 : ENNReal))
      (f := (u : ℝ → ℂ)) two_ne_zero ENNReal.ofNat_ne_top
      (Lp.eLpNorm_lt_top u)
  have hzero_le_total :
      (∫⁻ x, symmetricWindowTail u 0 x ∂(volume : Measure ℝ)) ≤
        (∫⁻ x, ‖(u : ℝ → ℂ) x‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ)) := by
    apply lintegral_mono
    intro x
    simp only [symmetricWindowTail, Set.indicator_apply]
    split_ifs <;> simp
  have hzero_lt_top := hzero_le_total.trans_lt htotal_lt_top
  have hzero_ne_top := hzero_lt_top.ne
  have hanti : ∀ x, Antitone (fun n => symmetricWindowTail u n x) := by
    intro x m n hmn
    by_cases hm : x ∈ Set.Icc (-(m : ℝ)) (m : ℝ)
    · have hn : x ∈ Set.Icc (-(n : ℝ)) (n : ℝ) := by
        have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
        exact Set.Icc_subset_Icc (by linarith) hmnR hm
      simp [symmetricWindowTail, hm, hn]
    · by_cases hn : x ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
      · simp [symmetricWindowTail, hm, hn]
      · simp [symmetricWindowTail, hm, hn]
  have hinterval_eventually (x : ℝ) :
      ∀ᶠ n : ℕ in atTop, x ∈ Set.Icc (-(n : ℝ)) (n : ℝ) := by
    have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    filter_upwards [hn.eventually (eventually_ge_atTop |x|)] with n hnx
    constructor <;> dsimp
    · nlinarith [neg_abs_le x]
    · nlinarith [le_abs_self x]
  have hpoint (x : ℝ) :
      Tendsto (fun n => symmetricWindowTail u n x) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hinterval_eventually x] with n hn
    simp [symmetricWindowTail, hn]
  have hlintegral := lintegral_tendsto_of_tendsto_of_antitone
    hmeas (ae_of_all _ hanti) hzero_ne_top (ae_of_all _ hpoint)
  simpa [symmetricWindowTail] using hlintegral

private theorem tendsto_symmetricWindowTail_eLpNorm
    (u : cc20GlobalLogCrossingL2) :
    Tendsto
      (fun n : ℕ => eLpNorm
        ((Set.Icc (-(n : ℝ)) (n : ℝ))ᶜ.indicator (fun x => (u : ℝ → ℂ) x))
        (2 : ENNReal) (volume : Measure ℝ))
      atTop (𝓝 0) := by
  have hlin := tendsto_symmetricWindowTail_lintegral u
  have hpow : Tendsto
      (fun n : ℕ =>
        (∫⁻ x, symmetricWindowTail u n x ∂(volume : Measure ℝ)) ^ (1 / 2 : ℝ))
      atTop (𝓝 ((0 : ENNReal) ^ (1 / 2 : ℝ))) :=
    (ENNReal.continuous_rpow_const.tendsto 0).comp hlin
  have hnorm (n : ℕ) :
      eLpNorm
          ((Set.Icc (-(n : ℝ)) (n : ℝ))ᶜ.indicator (fun x => (u : ℝ → ℂ) x))
          (2 : ENNReal) (volume : Measure ℝ) =
        (∫⁻ x, symmetricWindowTail u n x ∂(volume : Measure ℝ)) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofNat]
    congr 1
    apply lintegral_congr_ae
    exact ae_of_all _ fun x => by
      by_cases hx : x ∈ Set.Icc (-(n : ℝ)) (n : ℝ) <;>
        simp [symmetricWindowTail, hx]
  simpa [hnorm] using hpow

/-- Expanding symmetric interval projections converge strongly on the global
logarithmic L2 carrier. -/
theorem tendsto_kernelIntervalProjection_symmetric_apply
    (u : cc20GlobalLogCrossingL2) :
    Tendsto
      (fun n : ℕ => kernelIntervalProjection (-(n : ℝ)) (n : ℝ) 0 u)
      atTop (𝓝 u) := by
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  have herror (n : ℕ) :
      eLpNorm
          ((kernelIntervalProjection (-(n : ℝ)) (n : ℝ) 0 u :
            ℝ → ℂ) - (u : ℝ → ℂ))
          (2 : ENNReal) (volume : Measure ℝ) =
        eLpNorm
          ((Set.Icc (-(n : ℝ)) (n : ℝ))ᶜ.indicator
            (fun x => (u : ℝ → ℂ) x))
          (2 : ENNReal) (volume : Measure ℝ) := by
    apply eLpNorm_congr_norm_ae
    filter_upwards [kernelIntervalProjection_coeFn
      (-(n : ℝ)) (n : ℝ) 0 u] with x hx
    simp only [Pi.sub_apply]
    have hx' : (kernelIntervalProjection (-(n : ℝ)) (n : ℝ) 0 u : ℝ → ℂ) x =
        (Set.Icc (-(n : ℝ)) (n : ℝ)).indicator (fun t => (u : ℝ → ℂ) t) x := by
      simpa only [sub_zero, add_zero] using hx
    rw [hx']
    by_cases hmem : x ∈ Set.Icc (-(n : ℝ)) (n : ℝ) <;>
      simp [Set.indicator, hmem]
  have herror_tendsto : Tendsto
      (fun n : ℕ => eLpNorm
        ((kernelIntervalProjection (-(n : ℝ)) (n : ℝ) 0 u : ℝ → ℂ) -
          (u : ℝ → ℂ))
        (2 : ENNReal) (volume : Measure ℝ)) atTop (𝓝 0) := by
    simpa only [herror] using tendsto_symmetricWindowTail_eLpNorm u
  simpa [Lp.toLp_coeFn] using
    (Lp.tendsto_Lp_of_tendsto_eLpNorm
      (u : ℝ → ℂ) (Lp.memLp u) herror_tendsto)

end Dev
end ConnesWeilRH
