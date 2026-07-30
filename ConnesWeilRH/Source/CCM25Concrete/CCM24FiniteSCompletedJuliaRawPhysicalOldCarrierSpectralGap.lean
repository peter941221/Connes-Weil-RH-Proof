/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction

/-!
# Uniform old-carrier spectral-gap producer

The old-carrier reduction leaves one genuine lower-bound problem.  This file
records the exact sufficient producer: a family-uniform spectral gap for the
packed old-carrier analysis, together with a family-uniform operator-norm bound
for the reduced raw row.  The resulting Douglas constant is explicit:

```text
  C = rawBound / sqrt gap.
```

No source-specific spectral gap is asserted here.  The approximate-kernel
theorem at the end records the converse obstruction to any such family.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGap

open scoped InnerProduct InnerProductSpace
open scoped Topology

open CC20Concrete
open CCM24FiniteSDouglasFactor
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSCompletedJuliaRawDouglasReadout
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSCompletedJuliaRawPhysicalReadout

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## General spectral-gap adapter -/

theorem normSq_le_of_spectralGap_of_norm_le
    {H E G : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (A : H →L[ℂ] G) (B : H →L[ℂ] E)
    (gap rawBound : ℝ)
    (hgap : 0 < gap)
    (hgap_norm : ∀ x : H, gap * ‖x‖ ^ 2 ≤ ‖B x‖ ^ 2)
    (hrawBound : 0 ≤ rawBound)
    (hrawNorm : ‖A‖ ≤ rawBound) (x : H) :
    ‖A x‖ ^ 2 ≤
      (rawBound / Real.sqrt gap) ^ 2 * ‖B x‖ ^ 2 := by
  have hsqrt_pos : 0 < Real.sqrt gap := Real.sqrt_pos.2 hgap
  have hsqrt_sq : (Real.sqrt gap) ^ 2 = gap :=
    Real.sq_sqrt hgap.le
  have hbound : 0 ≤ rawBound / Real.sqrt gap :=
    div_nonneg hrawBound hsqrt_pos.le
  have hAx : ‖A x‖ ≤ rawBound * ‖x‖ := by
    calc
      ‖A x‖ ≤ ‖A‖ * ‖x‖ := A.le_opNorm x
      _ ≤ rawBound * ‖x‖ :=
        mul_le_mul_of_nonneg_right hrawNorm (norm_nonneg _)
  have hx_div : ‖x‖ ^ 2 ≤ ‖B x‖ ^ 2 / gap := by
    apply (le_div_iff₀ hgap).2
    simpa [mul_comm] using hgap_norm x
  have hx_scaled :
      ‖x‖ ≤ (1 / Real.sqrt gap) * ‖B x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (div_nonneg zero_le_one hsqrt_pos.le)
        (norm_nonneg _))).mp
    calc
      ‖x‖ ^ 2 ≤ ‖B x‖ ^ 2 / gap := hx_div
      _ = ‖B x‖ ^ 2 / (Real.sqrt gap) ^ 2 := by rw [hsqrt_sq]
      _ = ((1 / Real.sqrt gap) * ‖B x‖) ^ 2 := by
        field_simp [ne_of_gt hsqrt_pos]
  have hnorm :
      ‖A x‖ ≤ (rawBound / Real.sqrt gap) * ‖B x‖ := by
    calc
      ‖A x‖ ≤ rawBound * ‖x‖ := hAx
      _ ≤ rawBound * ((1 / Real.sqrt gap) * ‖B x‖) :=
        mul_le_mul_of_nonneg_left hx_scaled hrawBound
      _ = (rawBound / Real.sqrt gap) * ‖B x‖ := by ring
  have hsq := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hbound (norm_nonneg _))).mpr hnorm
  simpa only [mul_pow] using hsq

theorem exists_factor_of_spectralGap_of_norm_le
    {H E G : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (A : H →L[ℂ] G) (B : H →L[ℂ] E)
    (gap rawBound : ℝ)
    (hgap : 0 < gap)
    (hgap_norm : ∀ x : H, gap * ‖x‖ ^ 2 ≤ ‖B x‖ ^ 2)
    (hrawBound : 0 ≤ rawBound)
    (hrawNorm : ‖A‖ ≤ rawBound) :
    ∃ F : E →L[ℂ] G,
      ‖F‖ ≤ rawBound / Real.sqrt gap ∧ F ∘L B = A := by
  apply exists_factor_of_norm_sq_le A B (rawBound / Real.sqrt gap)
    (div_nonneg hrawBound (Real.sqrt_pos.2 hgap).le)
  exact normSq_le_of_spectralGap_of_norm_le A B gap rawBound hgap
    hgap_norm hrawBound hrawNorm

/-! ## Old-carrier family contracts -/

structure SuffixRawOldCarrierUniformSpectralGapData
    (lambda : CCM24SoninScale) (gap : ℝ) where
  gap_pos : 0 < gap
  lower_bound : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (y : finiteSCarrier),
    gap * ‖y‖ ^ 2 ≤
      ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S y‖ ^ 2

structure SuffixRawOldCarrierUniformRawNormData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (rawBound : ℝ) where
  raw_bound_nonneg : 0 ≤ rawBound
  raw_norm_le : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    ‖suffixActualBandRawPhysicalReducedRow owner lambda p S‖ ≤ rawBound

structure SuffixRawOldCarrierUniformDominationData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (bound : ℝ) where
  bound_nonneg : 0 ≤ bound
  domination : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
    SuffixRawOldCarrierDomination owner lambda p S bound

theorem suffixRawOldCarrierDomination_of_spectralGap_of_rawNorm
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (gap rawBound : ℝ)
    (hgap : 0 < gap)
    (hgap_norm : ∀ y : finiteSCarrier,
      gap * ‖y‖ ^ 2 ≤
        ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S y‖ ^ 2)
    (hrawBound : 0 ≤ rawBound)
    (hrawNorm : ‖suffixActualBandRawPhysicalReducedRow owner lambda p S‖ ≤
      rawBound) :
    SuffixRawOldCarrierDomination owner lambda p S
      (rawBound / Real.sqrt gap) := by
  have hbound : 0 ≤ rawBound / Real.sqrt gap :=
    div_nonneg hrawBound (Real.sqrt_pos.2 hgap).le
  refine ⟨hbound, ?_⟩
  intro y
  exact normSq_le_of_spectralGap_of_norm_le
    (suffixActualBandRawPhysicalReducedRow owner lambda p S)
    (suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)
    gap rawBound hgap hgap_norm hrawBound hrawNorm y

noncomputable def suffixRawOldCarrierUniformDominationDataOfSpectralGap
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (gap rawBound : ℝ)
    (gapData : SuffixRawOldCarrierUniformSpectralGapData lambda gap)
    (rawData : SuffixRawOldCarrierUniformRawNormData owner lambda rawBound) :
    SuffixRawOldCarrierUniformDominationData owner lambda
      (rawBound / Real.sqrt gap) :=
  { bound_nonneg :=
      div_nonneg rawData.raw_bound_nonneg
        (Real.sqrt_pos.2 gapData.gap_pos).le
    domination := fun p S =>
      suffixRawOldCarrierDomination_of_spectralGap_of_rawNorm owner lambda p S
        gap rawBound gapData.gap_pos (gapData.lower_bound p S)
        rawData.raw_bound_nonneg (rawData.raw_norm_le p S) }

noncomputable def suffixRawAmbientBoundaryUniformDominationDataOfSpectralGap
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (gap rawBound : ℝ)
    (gapData : SuffixRawOldCarrierUniformSpectralGapData lambda gap)
    (rawData : SuffixRawOldCarrierUniformRawNormData owner lambda rawBound) :
    SuffixRawAmbientBoundaryUniformDominationData owner lambda
      (rawBound / Real.sqrt gap) := by
  let oldData := suffixRawOldCarrierUniformDominationDataOfSpectralGap
    owner lambda gap rawBound gapData rawData
  refine
    { bound_nonneg := oldData.bound_nonneg
      domination := fun p S => ?_ }
  exact suffixRawOldCarrierDomination_implies_rawDomination owner lambda p S
    (rawBound / Real.sqrt gap) (oldData.domination p S)

noncomputable def suffixRawAmbientBoundaryUniformReadoutDataOfSpectralGap
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (gap rawBound : ℝ)
    (gapData : SuffixRawOldCarrierUniformSpectralGapData lambda gap)
  (rawData : SuffixRawOldCarrierUniformRawNormData owner lambda rawBound) :
    SuffixRawAmbientBoundaryUniformReadoutData owner lambda
      (rawBound / Real.sqrt gap) :=
  (suffixRawAmbientBoundaryUniformDominationDataOfSpectralGap owner lambda
    gap rawBound gapData rawData).toReadout

theorem exists_uniform_suffixRawOldCarrierDomination_of_spectralGap_of_rawNorm
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (gap rawBound : ℝ)
    (gapData : SuffixRawOldCarrierUniformSpectralGapData lambda gap)
    (rawData : SuffixRawOldCarrierUniformRawNormData owner lambda rawBound) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
        (y : finiteSCarrier),
        ‖suffixActualBandRawPhysicalReducedRow owner lambda p S y‖ ^ 2 ≤
          C ^ 2 *
            ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S y‖ ^ 2 := by
  let data := suffixRawAmbientBoundaryUniformDominationDataOfSpectralGap
    owner lambda gap rawBound gapData rawData
  refine ⟨rawBound / Real.sqrt gap, data.bound_nonneg, ?_⟩
  intro p S y
  exact
    (suffixRawOldCarrierDomination_of_spectralGap_of_rawNorm owner lambda p S
      gap rawBound gapData.gap_pos (gapData.lower_bound p S)
      rawData.raw_bound_nonneg (rawData.raw_norm_le p S)).2 y

/-! ## Approximate-kernel obstruction -/

theorem noExistsUniformOldCarrierDomination_of_approximateKernel
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    (prime : ℕ → CCM24VisiblePrime)
    (suffix : ℕ → List CCM24VisiblePrime)
    (y : ℕ → finiteSCarrier)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hraw : ∀ᶠ n in Filter.atTop,
      epsilon ≤
        ‖suffixActualBandRawPhysicalReducedRow owner lambda (prime n)
          (suffix n) (y n)‖)
    (hanalysis : Filter.Tendsto
      (fun n =>
        ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda (prime n)
          (suffix n) (y n)‖)
      Filter.atTop (𝓝 0)) :
    ¬ ∃ bound : ℝ,
      Nonempty
        (SuffixRawOldCarrierUniformDominationData owner lambda bound) := by
  rintro ⟨bound, ⟨data⟩⟩
  have hbound : 0 ≤ bound := data.bound_nonneg
  have hdenom : 0 < bound + 1 := by linarith
  have hdelta : 0 < epsilon / (bound + 1) :=
    div_pos hepsilon hdenom
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (Metric.tendsto_nhds.mp hanalysis (epsilon / (bound + 1)) hdelta)
  obtain ⟨n, hn⟩ :=
    (hraw.and (Filter.eventually_ge_atTop N)).exists
  have hsmallDist := hN n hn.2
  have hsmall :
      ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda (prime n)
          (suffix n) (y n)‖ < epsilon / (bound + 1) := by
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hsmallDist
  have hsq := (data.domination (prime n) (suffix n)).2 (y n)
  have hnorm :
      ‖suffixActualBandRawPhysicalReducedRow owner lambda (prime n)
          (suffix n) (y n)‖ ≤
        bound *
          ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda (prime n)
            (suffix n) (y n)‖ := by
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hbound (norm_nonneg _))).mp
    simpa [mul_pow] using hsq
  have hscaled :
      bound *
          ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda (prime n)
            (suffix n) (y n)‖ ≤
        bound * (epsilon / (bound + 1)) :=
    mul_le_mul_of_nonneg_left hsmall.le hbound
  have hratio : bound * (epsilon / (bound + 1)) < epsilon := by
    calc
      bound * (epsilon / (bound + 1)) =
          (bound * epsilon) / (bound + 1) := by ring
      _ < epsilon := by
        apply (div_lt_iff₀ hdenom).2
        nlinarith
  have hlt :
      ‖suffixActualBandRawPhysicalReducedRow owner lambda (prime n)
          (suffix n) (y n)‖ < epsilon :=
    lt_of_le_of_lt hnorm (hscaled.trans_lt hratio)
  exact (not_lt_of_ge hn.1) hlt

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGap
end CCM25Concrete
end Source
end ConnesWeilRH
