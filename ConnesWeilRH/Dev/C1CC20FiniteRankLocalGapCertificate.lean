/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20FiniteRankGapCertificate

/-!
# ROOT-local CC20 finite-rank gap certificate

CC20 Fact 1 controls the displacement-profile error only on the interval
visible from the ROOT square, not on the whole real line.  This leaf makes
that locality explicit.  Zero-extending the profile outside
`[-log 2, log 2]` leaves the ROOT-window kernel unchanged, so the existing
equation-(121) pairing engine consumes the local mass without strengthening
the paper's hypothesis.

The older whole-line certificate remains available as a strictly stronger
compatibility input through `CC20FiniteRankGapCertificate.toLocalCertificate`.

Reference: equations (115), (119)--(121) of
<https://arxiv.org/html/2006.13771>.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20FiniteRankLocalGapCertificate

open MeasureTheory
open C1CC20FiniteRankApproximation C1CC20FiniteRankDifference
  C1CC20FiniteRankGapCertificate C1CC20DisplacementKernel C1CC20KernelLpLift
  C1CC20LpOperator C1CC20PairingOperatorNorm C1CC20OperatorGap
  C1CC20RawKernelMass C1CC20RootWindowOperator
  C1CC20WindowedDisplacementReadback C1CC20WindowedPairingReadback

/-- Zero extension of a displacement profile to the interval actually visible
from the ROOT square window. -/
noncomputable def cc20RootLocalizedProfile (a : ℝ -> ℂ) : ℝ -> ℂ :=
  cc20RootDisplacementWindow.indicator a

/-- Localizing a profile to the ROOT displacement interval does not alter its
square-window kernel. -/
theorem windowedDisplacementKernel_eq_rootLocalizedProfile (a : ℝ -> ℂ) :
    windowedDisplacementKernel a cc20RootHalfWidth =
      windowedDisplacementKernel (cc20RootLocalizedProfile a) cc20RootHalfWidth := by
  funext p
  by_cases hp : p ∈ cc20WindowPair cc20RootHalfWidth
  · have hv : p.2 - p.1 ∈ cc20RootDisplacementWindow :=
      sub_mem_cc20RootDisplacementWindow hp.1 hp.2
    rw [windowedDisplacementKernel, windowedDisplacementKernel,
      Set.indicator_of_mem hp, Set.indicator_of_mem hp,
      displacementKernel, displacementKernel, cc20RootLocalizedProfile,
      Set.indicator_of_mem hv]
  · rw [windowedDisplacementKernel, windowedDisplacementKernel,
      Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]

/-- The equation-(115) profile difference, zero outside the ROOT displacement
interval.  This is the exact profile whose mass CC20 Fact 1 can supply. -/
noncomputable def cc20FiniteRankDifferenceRootProfile {ι : Type*} [Fintype ι]
    (endpointData : CC20Concrete.CC20EndpointSpectralData)
    (finiteData : CC20FiniteRankData ι) : ℝ -> ℂ :=
  cc20RootLocalizedProfile
    (cc20FiniteRankDifferenceProfile endpointData finiteData)

/-- The concrete finite-rank gap kernel reads only the ROOT-local profile. -/
theorem cc20FiniteRankDifferenceKernel_eq_windowedDisplacementKernel_rootProfile
    {ι : Type*} [Fintype ι]
    (endpointData : CC20Concrete.CC20EndpointSpectralData)
    (finiteData : CC20FiniteRankData ι) :
    cc20FiniteRankDifferenceKernel endpointData finiteData =
      windowedDisplacementKernel
        (cc20FiniteRankDifferenceRootProfile endpointData finiteData)
        cc20RootHalfWidth := by
  calc
    cc20FiniteRankDifferenceKernel endpointData finiteData =
        windowedDisplacementKernel
          (cc20FiniteRankDifferenceProfile endpointData finiteData)
          cc20RootHalfWidth :=
      cc20FiniteRankDifferenceKernel_eq_windowedDisplacementKernel
        endpointData finiteData
    _ = windowedDisplacementKernel
          (cc20FiniteRankDifferenceRootProfile endpointData finiteData)
          cc20RootHalfWidth := by
      simpa only [cc20FiniteRankDifferenceRootProfile] using
        (windowedDisplacementKernel_eq_rootLocalizedProfile
          (cc20FiniteRankDifferenceProfile endpointData finiteData))

/-- The independently certifiable ROOT-local facts about the CC20 profile
difference.  Its mass is the full symmetric displacement mass over
`[-log 2, log 2]`, represented as the whole-line integral of its zero
extension. -/
structure CC20FiniteRankLocalGapCertificate {ι : Type*} [Fintype ι]
    (endpointData : CC20Concrete.CC20EndpointSpectralData)
    (finiteData : CC20FiniteRankData ι)
    (gapData : CC20OperatorGapData (Lp ℂ 2 (volume : Measure ℝ))) where
  profile_aestronglyMeasurable :
    AEStronglyMeasurable
      (cc20FiniteRankDifferenceRootProfile endpointData finiteData) volume
  profile_norm_integrable :
    Integrable
      (fun v => ‖cc20FiniteRankDifferenceRootProfile endpointData finiteData v‖)
      volume
  profile_norm_mass_le_epsilon1 :
    (∫ v, ‖cc20FiniteRankDifferenceRootProfile endpointData finiteData v‖) ≤
      gapData.epsilon1

/-- A whole-line profile certificate is strictly stronger than the ROOT-local
one and therefore projects to it without any new numerical assumption. -/
noncomputable def CC20FiniteRankGapCertificate.toLocalCertificate
    {ι : Type*} [Fintype ι]
    (endpointData : CC20Concrete.CC20EndpointSpectralData)
    (finiteData : CC20FiniteRankData ι)
    (gapData : CC20OperatorGapData (Lp ℂ 2 (volume : Measure ℝ)))
    (certificate : CC20FiniteRankGapCertificate endpointData finiteData gapData) :
    CC20FiniteRankLocalGapCertificate endpointData finiteData gapData := by
  have hnorm :
      (fun v => ‖cc20FiniteRankDifferenceRootProfile endpointData finiteData v‖) =
        cc20RootDisplacementWindow.indicator
          (fun v => ‖cc20FiniteRankDifferenceProfile endpointData finiteData v‖) := by
    funext v
    by_cases hv : v ∈ cc20RootDisplacementWindow <;>
      simp [cc20FiniteRankDifferenceRootProfile, cc20RootLocalizedProfile, hv]
  have hlocal_integrable :
      Integrable
        (fun v => ‖cc20FiniteRankDifferenceRootProfile endpointData finiteData v‖)
        volume := by
    rw [hnorm]
    exact certificate.profile_norm_integrable.indicator
      measurableSet_cc20RootDisplacementWindow
  refine
    { profile_aestronglyMeasurable := ?_
      profile_norm_integrable := hlocal_integrable
      profile_norm_mass_le_epsilon1 := ?_ }
  · simpa only [cc20FiniteRankDifferenceRootProfile, cc20RootLocalizedProfile] using
      certificate.profile_aestronglyMeasurable.indicator
        measurableSet_cc20RootDisplacementWindow
  · rw [hnorm]
    calc
      ∫ v, cc20RootDisplacementWindow.indicator
          (fun v => ‖cc20FiniteRankDifferenceProfile endpointData finiteData v‖) v ≤
          ∫ v, ‖cc20FiniteRankDifferenceProfile endpointData finiteData v‖ := by
        refine integral_mono_ae
          (certificate.profile_norm_integrable.indicator
            measurableSet_cc20RootDisplacementWindow)
          certificate.profile_norm_integrable ?_
        filter_upwards with v
        by_cases hv : v ∈ cc20RootDisplacementWindow <;> simp [hv]
      _ ≤ gapData.epsilon1 := certificate.profile_norm_mass_le_epsilon1

/-- The local profile certificate bounds every Hilbert pairing of the concrete
finite-rank difference kernel. -/
theorem norm_inner_applyKernelLp_cc20FiniteRankDifference_le_of_localCertificate
    {ι : Type*} [Fintype ι]
    (endpointData : CC20Concrete.CC20EndpointSpectralData)
    (finiteData : CC20FiniteRankData ι)
    (gapData : CC20OperatorGapData (Lp ℂ 2 (volume : Measure ℝ)))
    (certificate : CC20FiniteRankLocalGapCertificate endpointData finiteData gapData)
    (hendpoint : MemLp
      (endpointKernelOnSquare endpointData cc20RootHalfWidth) 2 volume)
    (eta xi : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖inner ℂ eta
      (applyKernelLp (cc20FiniteRankDifferenceKernel endpointData finiteData)
        (memLp_cc20FiniteRankDifferenceKernel endpointData finiteData hendpoint) xi)‖ ≤
      gapData.epsilon1 * ‖eta‖ * ‖xi‖ := by
  let kernel : ℝ × ℝ → ℂ := cc20FiniteRankDifferenceKernel endpointData finiteData
  let hkernel : MemLp kernel 2 volume :=
    memLp_cc20FiniteRankDifferenceKernel endpointData finiteData hendpoint
  have hkernel_eq : kernel =
      windowedDisplacementKernel
        (cc20FiniteRankDifferenceRootProfile endpointData finiteData)
        cc20RootHalfWidth := by
    exact cc20FiniteRankDifferenceKernel_eq_windowedDisplacementKernel_rootProfile
      endpointData finiteData
  have houtput :
      ((applyKernelLp kernel hkernel xi : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
        applyKernel kernel (xi : ℝ → ℂ) := by
    change
      ((memLp_applyKernel_two hkernel (Lp.memLp xi)).toLp
        (applyKernel kernel (xi : ℝ → ℂ)) : ℝ → ℂ) =ᵐ[volume] _
    exact (memLp_applyKernel_two hkernel (Lp.memLp xi)).coeFn_toLp
  have hinner :
      inner ℂ eta (applyKernelLp kernel hkernel xi) =
        ∫ x : ℝ, star ((eta : ℝ → ℂ) x) * applyKernel kernel (xi : ℝ → ℂ) x := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [houtput] with x hx
    simp only [RCLike.inner_apply, hx]
    exact mul_comm _ _
  have hraw :=
    norm_pairing_applyKernel_windowedDisplacementKernel_le_of_l1Weight
      (a := cc20FiniteRankDifferenceRootProfile endpointData finiteData)
      (eta := fun x => star ((eta : ℝ → ℂ) x)) (xi := (xi : ℝ → ℂ))
      (r := cc20RootHalfWidth)
      certificate.profile_aestronglyMeasurable certificate.profile_norm_integrable
      (by simpa using (Lp.memLp eta).star) (by simpa using Lp.memLp xi)
  have hstarMass :=
    integral_norm_sq_cc20WindowZeroExtend_star_eq cc20RootHalfWidth eta
  have heta := l2Mass_cc20WindowZeroExtend_le cc20RootHalfWidth eta
  have hxi := l2Mass_cc20WindowZeroExtend_le cc20RootHalfWidth xi
  have hprofile_nonneg : 0 ≤
      ∫ v, ‖cc20FiniteRankDifferenceRootProfile endpointData finiteData v‖ :=
    integral_nonneg fun _ => norm_nonneg _
  rw [hinner, hkernel_eq]
  calc
    ‖∫ x : ℝ, star ((eta : ℝ → ℂ) x) *
        applyKernel
          (windowedDisplacementKernel
            (cc20FiniteRankDifferenceRootProfile endpointData finiteData)
            cc20RootHalfWidth)
          (xi : ℝ → ℂ) x‖ ≤
        (∫ x : ℝ,
          ‖cc20WindowZeroExtend cc20RootHalfWidth
            (fun y => star ((eta : ℝ → ℂ) y)) x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) *
          (∫ x : ℝ,
            ‖cc20WindowZeroExtend cc20RootHalfWidth (xi : ℝ → ℂ) x‖ ^ (2 : ℝ)) ^
              ((1 : ℝ) / 2) *
            ∫ v, ‖cc20FiniteRankDifferenceRootProfile endpointData finiteData v‖ := by
          simpa only using hraw
    _ =
        (∫ x : ℝ,
          ‖cc20WindowZeroExtend cc20RootHalfWidth (eta : ℝ → ℂ) x‖ ^ (2 : ℝ)) ^
            ((1 : ℝ) / 2) *
          (∫ x : ℝ,
            ‖cc20WindowZeroExtend cc20RootHalfWidth (xi : ℝ → ℂ) x‖ ^ (2 : ℝ)) ^
              ((1 : ℝ) / 2) *
            ∫ v, ‖cc20FiniteRankDifferenceRootProfile endpointData finiteData v‖ := by
          rw [hstarMass]
    _ ≤ ‖eta‖ * ‖xi‖ * gapData.epsilon1 := by
      have hmass :
          (∫ x : ℝ,
            ‖cc20WindowZeroExtend cc20RootHalfWidth (eta : ℝ → ℂ) x‖ ^ (2 : ℝ)) ^
              ((1 : ℝ) / 2) *
            (∫ x : ℝ,
              ‖cc20WindowZeroExtend cc20RootHalfWidth (xi : ℝ → ℂ) x‖ ^ (2 : ℝ)) ^
                ((1 : ℝ) / 2) ≤
              ‖eta‖ * ‖xi‖ := by
        exact mul_le_mul heta hxi
          (by positivity)
          (norm_nonneg _)
      exact mul_le_mul hmass certificate.profile_norm_mass_le_epsilon1
        hprofile_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = gapData.epsilon1 * ‖eta‖ * ‖xi‖ := by ring

/-- The ROOT-local profile certificate supplies the equation-(121) pairing
bound for the concrete operator gap `K_I - T`. -/
theorem cc20FiniteRankGap_pairingBound_of_localCertificate
    {ι : Type*} [Fintype ι]
    (endpointData : CC20Concrete.CC20EndpointSpectralData)
    (finiteData : CC20FiniteRankData ι)
    (gapData : CC20OperatorGapData (Lp ℂ 2 (volume : Measure ℝ)))
    (certificate : CC20FiniteRankLocalGapCertificate endpointData finiteData gapData)
    (hendpoint : MemLp
      (endpointKernelOnSquare endpointData cc20RootHalfWidth) 2 volume) :
    ∀ eta xi : Lp ℂ 2 (volume : Measure ℝ),
      ‖inner ℂ eta
        ((applyKernelLp (endpointKernelOnSquare endpointData cc20RootHalfWidth)
          hendpoint - cc20FiniteRankOperator finiteData) xi)‖ ≤
        gapData.epsilon1 * ‖eta‖ * ‖xi‖ := by
  intro eta xi
  rw [← applyKernelLp_cc20FiniteRankDifferenceKernel_eq_operatorGap
    endpointData finiteData hendpoint]
  exact norm_inner_applyKernelLp_cc20FiniteRankDifference_le_of_localCertificate
    endpointData finiteData gapData certificate hendpoint eta xi

/-- The ROOT-local equation-(115) mass becomes the operator-norm gap required
by CC20 equation (121). -/
theorem cc20FiniteRankGapNorm_le_of_localCertificate
    {ι : Type*} [Fintype ι]
    (endpointData : CC20Concrete.CC20EndpointSpectralData)
    (finiteData : CC20FiniteRankData ι)
    (gapData : CC20OperatorGapData (Lp ℂ 2 (volume : Measure ℝ)))
    (certificate : CC20FiniteRankLocalGapCertificate endpointData finiteData gapData)
    (hendpoint : MemLp
      (endpointKernelOnSquare endpointData cc20RootHalfWidth) 2 volume) :
    ‖applyKernelLp (endpointKernelOnSquare endpointData cc20RootHalfWidth)
      hendpoint - cc20FiniteRankOperator finiteData‖ ≤ gapData.epsilon1 := by
  exact cc20GapNorm_le_of_pairingBound gapData
    (applyKernelLp (endpointKernelOnSquare endpointData cc20RootHalfWidth) hendpoint)
    (cc20FiniteRankOperator finiteData)
    (cc20FiniteRankGap_pairingBound_of_localCertificate
      endpointData finiteData gapData certificate hendpoint)

/-- The ROOT-local profile certificate feeds directly into the rank-one
conclusion of CC20 Lemma `second` once the independent coercivity input for
`T` is present. -/
theorem cc20FiniteRankNegativeForm_le_rankOne_of_localCertificate
    {ι : Type*} [Fintype ι]
    (endpointData : CC20Concrete.CC20EndpointSpectralData)
    (finiteData : CC20FiniteRankData ι)
    (gapData : CC20OperatorGapData (Lp ℂ 2 (volume : Measure ℝ)))
    (certificate : CC20FiniteRankLocalGapCertificate endpointData finiteData gapData)
    (hendpoint : MemLp
      (endpointKernelOnSquare endpointData cc20RootHalfWidth) 2 volume)
    {ell : Lp ℂ 2 (volume : Measure ℝ) → ℝ}
    (hT : ∀ xi,
      cc20DefectQuadraticForm (cc20FiniteRankOperator finiteData) xi +
          gapData.a * (ell xi) ^ 2 ≥ gapData.epsilon2 * ‖xi‖ ^ 2) :
    ∀ xi,
      -(2 * gapData.ePrime) *
          cc20DefectQuadraticForm
            (applyKernelLp (endpointKernelOnSquare endpointData cc20RootHalfWidth) hendpoint) xi ≤
        gapData.gamma * (ell xi) ^ 2 := by
  exact cc20NegativeForm_le_rankOne_of_pairingBound gapData
    (applyKernelLp (endpointKernelOnSquare endpointData cc20RootHalfWidth) hendpoint)
    (cc20FiniteRankOperator finiteData) hT
    (cc20FiniteRankGap_pairingBound_of_localCertificate
      endpointData finiteData gapData certificate hendpoint)

end C1CC20FiniteRankLocalGapCertificate
end Source
end ConnesWeilRH
