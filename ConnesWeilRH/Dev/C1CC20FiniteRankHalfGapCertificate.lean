/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20FiniteRankLocalGapCertificate
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# CC20 Fact 1 half-interval certificate

CC20 Fact 1 is stated as `2 * integral_[0, log 2] |tau - chi|`, whereas the
ROOT-local operator certificate consumes the symmetric displacement mass.
This leaf proves that conversion.  The endpoint profile is even by its
`exp |v|` definition; the finite profile's evenness remains an explicit
structural producer obligation, to be discharged only from paired
`plus/minus`
frequency data.

Reference: equations (104), (114)--(115), and (121) of
<https://arxiv.org/html/2006.13771>.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20FiniteRankHalfGapCertificate

open MeasureTheory
open CC20Concrete
open C1CC20DisplacementKernel C1CC20FiniteRankApproximation
  C1CC20FiniteRankDifference C1CC20FiniteRankLocalGapCertificate
  C1CC20OperatorGap

/-- A real function continuous on a symmetric window has the expected
half-window identity.  This is kept local to the Fact-1 bridge so no DETECTOR
leaf is an analytic dependency of the CC20 gap route. -/
theorem intervalIntegral_symmetry_half_real (t : ℝ) (ht : 0 ≤ t) (f : ℝ → ℝ)
    (hfc : ContinuousOn f (Set.Icc (-t) t)) :
    ∫ x in -t..t, f x = ∫ x in 0..t, (f x + f (-x)) := by
  have hA : IntervalIntegrable f volume (-t) 0 :=
    (hfc.mono (Set.Icc_subset_Icc le_rfl ht)).intervalIntegrable_of_Icc
      (neg_nonpos.mpr ht)
  have hB : IntervalIntegrable f volume 0 t :=
    (hfc.mono (Set.Icc_subset_Icc (neg_nonpos.mpr ht) le_rfl)).intervalIntegrable_of_Icc ht
  have hB' : IntervalIntegrable (fun x : ℝ => f (-x)) volume 0 t := by
    simpa only [neg_zero, neg_neg] using
      (IntervalIntegrable.iff_comp_neg (f := f) (a := 0) (b := -t)).mp hA.symm
  rw [intervalIntegral.integral_add hB hB',
    intervalIntegral.integral_comp_neg (f := f) (a := 0) (b := t),
    neg_zero,
    ← intervalIntegral.integral_add_adjacent_intervals hA hB]
  ring

/-- The CC20 endpoint displacement profile is even: its scalar formula only
depends on the displacement through `|v|`. -/
theorem endpointDisplacementProfile_even
    (endpointData : CC20EndpointSpectralData) (v : ℝ) :
    endpointDisplacementProfile endpointData (-v) =
      endpointDisplacementProfile endpointData v := by
  simp [endpointDisplacementProfile, CC20EndpointSpectralData.endpointAdditiveKernel]

/-- Endpoint evenness and a separately proved finite-profile evenness give
the evenness of the equation-(115) difference profile. -/
theorem cc20FiniteRankDifferenceProfile_even_of_finiteProfile_even
    {ι : Type*} [Fintype ι]
    (endpointData : CC20EndpointSpectralData)
    (finiteData : CC20FiniteRankData ι)
    (hfinite : ∀ v : ℝ,
      cc20FiniteRankProfile finiteData (-v) = cc20FiniteRankProfile finiteData v)
    (v : ℝ) :
    cc20FiniteRankDifferenceProfile endpointData finiteData (-v) =
      cc20FiniteRankDifferenceProfile endpointData finiteData v := by
  change endpointDisplacementProfile endpointData (-v) -
      cc20FiniteRankProfile finiteData (-v) =
    endpointDisplacementProfile endpointData v - cc20FiniteRankProfile finiteData v
  rw [endpointDisplacementProfile_even, hfinite]

/-- A profile continuous on the ROOT displacement window has an integrable
norm after ROOT-local zero extension. -/
theorem integrable_norm_cc20RootLocalizedProfile_of_continuous
    (a : ℝ → ℂ) (ha : ContinuousOn a cc20RootDisplacementWindow) :
    Integrable (fun v => ‖cc20RootLocalizedProfile a v‖) volume := by
  have hnorm :
      (fun v => ‖cc20RootLocalizedProfile a v‖) =
        cc20RootDisplacementWindow.indicator (fun v => ‖a v‖) := by
    funext v
    by_cases hv : v ∈ cc20RootDisplacementWindow <;>
      simp [cc20RootLocalizedProfile, hv]
  rw [hnorm, integrable_indicator_iff measurableSet_cc20RootDisplacementWindow]
  simpa only [cc20RootDisplacementWindow] using
    ha.norm.integrableOn_Icc

/-- ROOT-window continuity supplies the local almost-strong measurability
needed after zero extension. -/
theorem aestronglyMeasurable_cc20RootLocalizedProfile_of_continuous
    (a : ℝ → ℂ) (ha : ContinuousOn a cc20RootDisplacementWindow) :
    AEStronglyMeasurable (cc20RootLocalizedProfile a) volume := by
  rw [cc20RootLocalizedProfile,
    aestronglyMeasurable_indicator_iff measurableSet_cc20RootDisplacementWindow]
  simpa only [cc20RootDisplacementWindow] using ha.integrableOn_Icc.aestronglyMeasurable

/-- The whole-line mass of the ROOT-local zero extension is exactly twice the
positive-half interval mass when the profile is even. -/
theorem integral_norm_cc20RootLocalizedProfile_eq_two_half
    (a : ℝ → ℂ) (ha : ContinuousOn a cc20RootDisplacementWindow)
  (heven : ∀ v : ℝ, a (-v) = a v) :
    (∫ v, ‖cc20RootLocalizedProfile a v‖) =
      2 * ∫ v in (0 : ℝ)..cc20RootLength, ‖a v‖ := by
  have hlength_nonneg : 0 ≤ cc20RootLength := cc20RootLength_pos.le
  have hwindow_le : -cc20RootLength ≤ cc20RootLength := by
    linarith [cc20RootLength_pos]
  have hnorm_even : ∀ v : ℝ, ‖a (-v)‖ = ‖a v‖ := fun v =>
    congrArg norm (heven v)
  have hpoint :
      (fun v : ℝ => ‖a v‖ + ‖a (-v)‖) =
        fun v : ℝ => 2 * ‖a v‖ := by
    funext v
    rw [hnorm_even]
    ring
  have hsymm :
      (∫ v in -cc20RootLength..cc20RootLength, ‖a v‖) =
        2 * ∫ v in (0 : ℝ)..cc20RootLength, ‖a v‖ := by
    rw [intervalIntegral_symmetry_half_real cc20RootLength cc20RootLength_pos.le
      (fun v : ℝ => ‖a v‖) (by simpa only [cc20RootDisplacementWindow] using ha.norm), hpoint,
      intervalIntegral.integral_const_mul]
  have hnorm :
      (fun v => ‖cc20RootLocalizedProfile a v‖) =
        cc20RootDisplacementWindow.indicator (fun v => ‖a v‖) := by
    funext v
    by_cases hv : v ∈ cc20RootDisplacementWindow <;>
      simp [cc20RootLocalizedProfile, hv]
  calc
    (∫ v, ‖cc20RootLocalizedProfile a v‖) =
        ∫ v in cc20RootDisplacementWindow, ‖a v‖ := by
      rw [hnorm, ← integral_indicator measurableSet_cc20RootDisplacementWindow]
    _ = ∫ v in -cc20RootLength..cc20RootLength, ‖a v‖ := by
      rw [cc20RootDisplacementWindow]
      calc
        (∫ v in Set.Icc (-cc20RootLength) cc20RootLength, ‖a v‖) =
            ∫ v in Set.Ioc (-cc20RootLength) cc20RootLength, ‖a v‖ :=
          integral_Icc_eq_integral_Ioc
        _ = ∫ v in -cc20RootLength..cc20RootLength, ‖a v‖ :=
          (intervalIntegral.integral_of_le
            (a := -cc20RootLength) (b := cc20RootLength)
            (f := fun v : ℝ => ‖a v‖) hwindow_le).symm
    _ = 2 * ∫ v in (0 : ℝ)..cc20RootLength, ‖a v‖ := hsymm

/-- The producer-facing form of CC20 Fact 1.  The finite profile evenness is
kept separate from the numerical mass inequality, so a future certificate
must trace it to explicit paired `plus/minus` frequency data. -/
structure CC20FiniteRankHalfGapCertificate {ι : Type*} [Fintype ι]
    (endpointData : CC20EndpointSpectralData)
    (finiteData : CC20FiniteRankData ι)
    (gapData : CC20OperatorGapData (Lp ℂ 2 (volume : Measure ℝ))) where
  difference_profile_continuousOn_root :
    ContinuousOn (cc20FiniteRankDifferenceProfile endpointData finiteData)
      cc20RootDisplacementWindow
  finite_profile_even : ∀ v : ℝ,
    cc20FiniteRankProfile finiteData (-v) = cc20FiniteRankProfile finiteData v
  two_half_norm_mass_le_epsilon1 :
    2 * (∫ v in (0 : ℝ)..cc20RootLength,
      ‖cc20FiniteRankDifferenceProfile endpointData finiteData v‖) ≤
        gapData.epsilon1

/-- CC20 Fact 1, once supplied with its analytic continuity and structural
finite-profile symmetry producers, creates the ROOT-local certificate used by
equation (121). -/
noncomputable def CC20FiniteRankHalfGapCertificate.toLocalCertificate
    {ι : Type*} [Fintype ι]
    (endpointData : CC20EndpointSpectralData)
    (finiteData : CC20FiniteRankData ι)
    (gapData : CC20OperatorGapData (Lp ℂ 2 (volume : Measure ℝ)))
    (certificate : CC20FiniteRankHalfGapCertificate endpointData finiteData gapData) :
    CC20FiniteRankLocalGapCertificate endpointData finiteData gapData := by
  let profile := cc20FiniteRankDifferenceProfile endpointData finiteData
  have hprofile_even : ∀ v : ℝ, profile (-v) = profile v := by
    intro v
    exact cc20FiniteRankDifferenceProfile_even_of_finiteProfile_even
      endpointData finiteData certificate.finite_profile_even v
  refine
    { profile_aestronglyMeasurable := ?_
      profile_norm_integrable := ?_
      profile_norm_mass_le_epsilon1 := ?_ }
  · exact aestronglyMeasurable_cc20RootLocalizedProfile_of_continuous
      profile certificate.difference_profile_continuousOn_root
  · exact integrable_norm_cc20RootLocalizedProfile_of_continuous
      profile certificate.difference_profile_continuousOn_root
  · calc
      (∫ v, ‖cc20FiniteRankDifferenceRootProfile endpointData finiteData v‖) =
          2 * ∫ v in (0 : ℝ)..cc20RootLength, ‖profile v‖ := by
        simpa only [cc20FiniteRankDifferenceRootProfile, profile] using
          (integral_norm_cc20RootLocalizedProfile_eq_two_half profile
            certificate.difference_profile_continuousOn_root hprofile_even)
      _ ≤ gapData.epsilon1 := by
        simpa only [profile] using certificate.two_half_norm_mass_le_epsilon1

end C1CC20FiniteRankHalfGapCertificate
end Source
end ConnesWeilRH
