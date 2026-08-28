/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20FiniteRankDifference
import ConnesWeilRH.Dev.C1CC20PairingOperatorNorm

/-!
# CC20 finite-rank gap certificate

This leaf is the final analytic interface between the numerical profile
estimate in CC20 equation (115) and the bounded-operator gap in equation
(121).  Its first reusable fact is that restriction to the ROOT window,
followed by zero extension, is an `L²` contraction.  The later certificate
will combine that fact with the existing `L¹ × L² × L²` pairing estimate.

Reference: equations (115), (119)--(121) of
<https://arxiv.org/html/2006.13771>.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20FiniteRankGapCertificate

open MeasureTheory
open C1CC20FiniteRankApproximation C1CC20FiniteRankDifference
  C1CC20DisplacementKernel C1CC20KernelLpLift C1CC20LpOperator
  C1CC20PairingOperatorNorm
  C1CC20OperatorGap C1CC20RawKernelMass C1CC20RootWindowOperator
  C1CC20WindowedDisplacementReadback C1CC20WindowedPairingReadback

/-- The `L²` quotient norm of a representative is its square-root mass. -/
theorem norm_toLp_eq_integral_norm_rpow_half
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖ =
      (∫ x : ℝ, ‖f x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
  calc
    ‖hf.toLp f‖ = lpNorm f 2 volume := by
      rw [Lp.norm_toLp, lpNorm, if_pos hf.aestronglyMeasurable]
    _ = (∫ x : ℝ, ‖f x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
      rw [lpNorm_eq_integral_norm_rpow_toReal
        (show (2 : ENNReal) ≠ 0 by norm_num) (by simp) hf.aestronglyMeasurable]
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, pow_two]
      ring_nf

/-- Zero extension from any CC20 window cannot increase the `L²` mass of an
ambient quotient representative. -/
theorem l2Mass_cc20WindowZeroExtend_le
    (r : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫ x : ℝ, ‖cc20WindowZeroExtend r (f : ℝ → ℂ) x‖ ^ (2 : ℝ)) ^
        ((1 : ℝ) / 2) ≤ ‖f‖ := by
  let hf : MemLp (f : ℝ → ℂ) 2 volume := Lp.memLp f
  let hwindow : MemLp (cc20WindowZeroExtend r (f : ℝ → ℂ)) 2 volume :=
    memLp_cc20WindowZeroExtend r hf
  have hwindowInt : Integrable
      (fun x : ℝ => ‖cc20WindowZeroExtend r (f : ℝ → ℂ) x‖ ^ (2 : ℕ)) :=
    (memLp_two_iff_integrable_sq_norm hwindow.1).mp hwindow
  have hfInt : Integrable (fun x : ℝ => ‖(f : ℝ → ℂ) x‖ ^ (2 : ℕ)) :=
    (memLp_two_iff_integrable_sq_norm hf.1).mp hf
  have hmass :
      (∫ x : ℝ, ‖cc20WindowZeroExtend r (f : ℝ → ℂ) x‖ ^ (2 : ℕ)) ≤
        ∫ x : ℝ, ‖(f : ℝ → ℂ) x‖ ^ (2 : ℕ) := by
    refine integral_mono_ae hwindowInt hfInt ?_
    filter_upwards with x
    by_cases hx : x ∈ cc20Window r <;>
      simp [cc20WindowZeroExtend, hx]
  have hwindowNormSq :
      ‖hwindow.toLp (cc20WindowZeroExtend r (f : ℝ → ℂ))‖ ^ (2 : ℕ) =
        ∫ x : ℝ, ‖cc20WindowZeroExtend r (f : ℝ → ℂ) x‖ ^ (2 : ℕ) :=
    norm_toLp_sq_eq_integral_norm_sq hwindow
  have hfNormSq : ‖f‖ ^ (2 : ℕ) =
      ∫ x : ℝ, ‖(f : ℝ → ℂ) x‖ ^ (2 : ℕ) := by
    calc
      ‖f‖ ^ (2 : ℕ) = ‖hf.toLp (f : ℝ → ℂ)‖ ^ (2 : ℕ) :=
        congrArg (fun u : Lp ℂ 2 volume => ‖u‖ ^ (2 : ℕ))
          (Lp.toLp_coeFn f hf).symm
      _ = ∫ x : ℝ, ‖(f : ℝ → ℂ) x‖ ^ (2 : ℕ) :=
        norm_toLp_sq_eq_integral_norm_sq hf
  have hquotient :
      ‖hwindow.toLp (cc20WindowZeroExtend r (f : ℝ → ℂ))‖ ≤ ‖f‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    calc
      ‖hwindow.toLp (cc20WindowZeroExtend r (f : ℝ → ℂ))‖ ^ (2 : ℕ) =
          ∫ x : ℝ, ‖cc20WindowZeroExtend r (f : ℝ → ℂ) x‖ ^ (2 : ℕ) :=
        hwindowNormSq
      _ ≤ ∫ x : ℝ, ‖(f : ℝ → ℂ) x‖ ^ (2 : ℕ) := hmass
      _ = ‖f‖ ^ (2 : ℕ) := hfNormSq.symm
  rw [← norm_toLp_eq_integral_norm_rpow_half hwindow]
  exact hquotient

/-- Conjugating an ambient `L²` representative leaves its zero-extended
square mass unchanged. -/
theorem integral_norm_sq_cc20WindowZeroExtend_star_eq
    (r : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫ x : ℝ,
      ‖cc20WindowZeroExtend r (fun y => star ((f : ℝ → ℂ) y)) x‖ ^ (2 : ℝ)) =
      ∫ x : ℝ, ‖cc20WindowZeroExtend r (f : ℝ → ℂ) x‖ ^ (2 : ℝ) := by
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ cc20Window r <;>
    simp [cc20WindowZeroExtend, hx]

/-- The independently certifiable numerical facts about the CC20 profile
difference.  The structure deliberately owns only the profile's analytic
regularity and its equation-(115) mass bound; the endpoint kernel's `L²`
owner remains a separate caller premise. -/
structure CC20FiniteRankGapCertificate {ι : Type*} [Fintype ι]
    (endpointData : CC20Concrete.CC20EndpointSpectralData)
    (finiteData : CC20FiniteRankData ι)
    (gapData : CC20OperatorGapData (Lp ℂ 2 (volume : Measure ℝ))) where
  profile_aestronglyMeasurable :
    AEStronglyMeasurable
      (cc20FiniteRankDifferenceProfile endpointData finiteData) volume
  profile_norm_integrable :
    Integrable (fun v => ‖cc20FiniteRankDifferenceProfile endpointData finiteData v‖)
      volume
  profile_norm_mass_le_epsilon1 :
    (∫ v, ‖cc20FiniteRankDifferenceProfile endpointData finiteData v‖) ≤
      gapData.epsilon1

/-- The equation-(115) profile certificate bounds every Hilbert pairing of
the concrete finite-rank difference kernel. -/
theorem norm_inner_applyKernelLp_cc20FiniteRankDifference_le_of_certificate
    {ι : Type*} [Fintype ι]
    (endpointData : CC20Concrete.CC20EndpointSpectralData)
    (finiteData : CC20FiniteRankData ι)
    (gapData : CC20OperatorGapData (Lp ℂ 2 (volume : Measure ℝ)))
    (certificate : CC20FiniteRankGapCertificate endpointData finiteData gapData)
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
        (cc20FiniteRankDifferenceProfile endpointData finiteData)
        cc20RootHalfWidth := by
    exact cc20FiniteRankDifferenceKernel_eq_windowedDisplacementKernel
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
      (a := cc20FiniteRankDifferenceProfile endpointData finiteData)
      (eta := fun x => star ((eta : ℝ → ℂ) x)) (xi := (xi : ℝ → ℂ))
      (r := cc20RootHalfWidth)
      certificate.profile_aestronglyMeasurable certificate.profile_norm_integrable
      (by simpa using (Lp.memLp eta).star) (by simpa using Lp.memLp xi)
  have hstarMass :=
    integral_norm_sq_cc20WindowZeroExtend_star_eq cc20RootHalfWidth eta
  have heta := l2Mass_cc20WindowZeroExtend_le cc20RootHalfWidth eta
  have hxi := l2Mass_cc20WindowZeroExtend_le cc20RootHalfWidth xi
  have hprofile_nonneg : 0 ≤
      ∫ v, ‖cc20FiniteRankDifferenceProfile endpointData finiteData v‖ :=
    integral_nonneg fun _ => norm_nonneg _
  rw [hinner, hkernel_eq]
  calc
    ‖∫ x : ℝ, star ((eta : ℝ → ℂ) x) *
        applyKernel
          (windowedDisplacementKernel
            (cc20FiniteRankDifferenceProfile endpointData finiteData)
            cc20RootHalfWidth)
          (xi : ℝ → ℂ) x‖ ≤
        (∫ x : ℝ,
          ‖cc20WindowZeroExtend cc20RootHalfWidth
            (fun y => star ((eta : ℝ → ℂ) y)) x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) *
          (∫ x : ℝ,
            ‖cc20WindowZeroExtend cc20RootHalfWidth (xi : ℝ → ℂ) x‖ ^ (2 : ℝ)) ^
              ((1 : ℝ) / 2) *
            ∫ v, ‖cc20FiniteRankDifferenceProfile endpointData finiteData v‖ := by
          simpa only using hraw
    _ =
        (∫ x : ℝ,
          ‖cc20WindowZeroExtend cc20RootHalfWidth (eta : ℝ → ℂ) x‖ ^ (2 : ℝ)) ^
            ((1 : ℝ) / 2) *
          (∫ x : ℝ,
            ‖cc20WindowZeroExtend cc20RootHalfWidth (xi : ℝ → ℂ) x‖ ^ (2 : ℝ)) ^
              ((1 : ℝ) / 2) *
            ∫ v, ‖cc20FiniteRankDifferenceProfile endpointData finiteData v‖ := by
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

/-- The profile certificate supplies the exact equation-(121) pairing bound
for the concrete operator gap `K_I - T`. -/
theorem cc20FiniteRankGap_pairingBound_of_certificate
    {ι : Type*} [Fintype ι]
    (endpointData : CC20Concrete.CC20EndpointSpectralData)
    (finiteData : CC20FiniteRankData ι)
    (gapData : CC20OperatorGapData (Lp ℂ 2 (volume : Measure ℝ)))
    (certificate : CC20FiniteRankGapCertificate endpointData finiteData gapData)
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
  exact norm_inner_applyKernelLp_cc20FiniteRankDifference_le_of_certificate
    endpointData finiteData gapData certificate hendpoint eta xi

/-- Equation-(115)'s certified profile mass becomes the operator-norm gap
required by CC20 equation (121). -/
theorem cc20FiniteRankGapNorm_le_of_certificate
    {ι : Type*} [Fintype ι]
    (endpointData : CC20Concrete.CC20EndpointSpectralData)
    (finiteData : CC20FiniteRankData ι)
    (gapData : CC20OperatorGapData (Lp ℂ 2 (volume : Measure ℝ)))
    (certificate : CC20FiniteRankGapCertificate endpointData finiteData gapData)
    (hendpoint : MemLp
      (endpointKernelOnSquare endpointData cc20RootHalfWidth) 2 volume) :
    ‖applyKernelLp (endpointKernelOnSquare endpointData cc20RootHalfWidth)
      hendpoint - cc20FiniteRankOperator finiteData‖ ≤ gapData.epsilon1 := by
  exact cc20GapNorm_le_of_pairingBound gapData
    (applyKernelLp (endpointKernelOnSquare endpointData cc20RootHalfWidth) hendpoint)
    (cc20FiniteRankOperator finiteData)
    (cc20FiniteRankGap_pairingBound_of_certificate
      endpointData finiteData gapData certificate hendpoint)

/-- The profile certificate feeds directly into the rank-one conclusion of
CC20 Lemma `second` once the independent coercivity input for `T` is present. -/
theorem cc20FiniteRankNegativeForm_le_rankOne_of_certificate
    {ι : Type*} [Fintype ι]
    (endpointData : CC20Concrete.CC20EndpointSpectralData)
    (finiteData : CC20FiniteRankData ι)
    (gapData : CC20OperatorGapData (Lp ℂ 2 (volume : Measure ℝ)))
    (certificate : CC20FiniteRankGapCertificate endpointData finiteData gapData)
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
    (cc20FiniteRankGap_pairingBound_of_certificate
      endpointData finiteData gapData certificate hendpoint)

end C1CC20FiniteRankGapCertificate
end Source
end ConnesWeilRH
