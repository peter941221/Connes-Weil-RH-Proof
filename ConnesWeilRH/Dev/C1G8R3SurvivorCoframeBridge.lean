/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3InternalProlateGapEnergy
import ConnesWeilRH.Dev.C1G8P1MetricChannels
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedSourcePolar
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurCascade
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSchurPolarTelescoping
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSTransportBounds
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSParameterizedEulerProduct

/-!
# Survivor coframe bridge: the G8 survivor diagonal leg on the source carrier

Map 042 bridge facts B1 and the S1/S2 assembly.  The survivor coframe factors
as the Euler upper factor times the source inclusion composed with a purely
source-side Schur leg, and the exact pointwise Pythagoras split of the full
norm at the Sonin projection converts the G8 survivor diagonal energy
obligation exactly into a pair of series on the source carrier:

* OUT (leakage band) `(I - P) C J` after the source-side Schur leg, already
  dominated by the selected-root source-Sonin leakage square-sum of
  `C1G8R3InternalProlateGapEnergy` via bounded right precomposition;
* IN (in-Sonin response) `J† C J` after the source-side Schur leg, the open
  survivor estimate target.

The main equivalence `g8SurvivorCoframe_energy_iff_sourceCarrier_inLeg` is
unconditional: the OUT leg needs no hypothesis, so the survivor diagonal
energy obligation is exactly the in-Sonin source-carrier square-sum.  No
estimate is claimed for the IN leg; RH is not touched.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source
open Source.CC20Concrete
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSFixedSourcePolar
open Source.CCM25Concrete.CCM24FiniteSActualSchurCascade
open Source.CCM25Concrete.CCM24FiniteSSchurPolarTelescoping
open Source.CCM25Concrete.CCM24FiniteSParameterizedEulerProduct
open Source.CCM25Concrete.CCM24FiniteSTransportBounds
open Source.CCM25Concrete.SelectedWeilSquare
open Source.C1G8P1MetricChannels
open scoped ENNReal InnerProduct InnerProductSpace

local notation "Carrier" => finiteSCarrier

noncomputable local instance survivorBridgeCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

private noncomputable def survivorBridgeBasisIndex
    (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] : Set G :=
  Classical.choose (exists_hilbertBasis ℂ G)

private noncomputable def survivorBridgeBasis
    (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] : HilbertBasis (survivorBridgeBasisIndex G) ℂ G :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ G))

/-- The purely source-side Schur leg of the survivor coframe: Gram
inverse-sqrt at the empty suffix, the visible-prime Euler transition adjoint,
and Gram inverse-sqrt at the visible suffix. -/
noncomputable def g8SurvivorSourceLeg
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  parameterizedSoninGramInvSqrt lambda 1 [] (by norm_num) ∘L
    (suffixEulerTransitionProduct lambda family.visiblePrimes)† ∘L
      parameterizedSoninGramInvSqrt lambda 1 family.visiblePrimes (by norm_num)

/-- The source inclusion is isometric. -/
theorem g8BridgeSourceInclusion_norm_map (lambda : CCM24SoninScale)
    (z : sourceSoninCarrier lambda) :
    ‖sourceInclusion lambda z‖ = ‖z‖ := by
  have hcomp := congrArg
    (fun T : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda =>
      T z) (sourceInclusion_adjoint_comp_self lambda)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    at hcomp
  have hstep : inner ℂ z
      ((sourceInclusion lambda).adjoint (sourceInclusion lambda z)) =
      inner ℂ (sourceInclusion lambda z) (sourceInclusion lambda z) :=
    ContinuousLinearMap.adjoint_inner_right (sourceInclusion lambda) z
      (sourceInclusion lambda z)
  rw [hcomp] at hstep
  have hsq : ‖sourceInclusion lambda z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), ← hstep]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with heq | heq
  · exact heq
  · linarith [norm_nonneg z, norm_nonneg (sourceInclusion lambda z)]

/-- Exact pointwise Pythagoras split at the Sonin projection: the range part
of the norm is transported back through the source inclusion isometry, so the
complement carries exactly the leakage band. -/
theorem g8BridgeSoninCarrier_normSq_split (lambda : CCM24SoninScale)
    (v : finiteSCarrier) :
    ‖v‖ ^ 2 =
      ‖(sourceInclusion lambda).adjoint v‖ ^ 2 +
        ‖(ContinuousLinearMap.id ℂ finiteSCarrier -
          sourceSoninProjection lambda) v‖ ^ 2 := by
  have hPM : sourceSoninProjection lambda *
      (ContinuousLinearMap.id ℂ finiteSCarrier -
        sourceSoninProjection lambda) = 0 := by
    simpa only [ContinuousLinearMap.one_def] using
      (sourceSoninProjection_isStarProjection lambda).mul_one_sub_self
  have hzero : (sourceInclusion lambda).adjoint
      ((ContinuousLinearMap.id ℂ finiteSCarrier -
        sourceSoninProjection lambda) v) = 0 := by
    have h1 := congrArg
      (fun T : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda =>
        T ((ContinuousLinearMap.id ℂ finiteSCarrier -
          sourceSoninProjection lambda) v))
      (sourceInclusionAdjoint_comp_sourceProjection lambda)
    have h2 := congrArg (fun T : finiteSCarrier →L[ℂ] finiteSCarrier =>
      T v) hPM
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.zero_apply] at h1 h2
    rw [h2, map_zero] at h1
    exact h1.symm
  have hdecomp : v = sourceInclusion lambda
      ((sourceInclusion lambda).adjoint v) +
      ((ContinuousLinearMap.id ℂ finiteSCarrier -
        sourceSoninProjection lambda) v) := by
    have h1 : sourceSoninProjection lambda v +
        ((ContinuousLinearMap.id ℂ finiteSCarrier -
          sourceSoninProjection lambda) v) = v := by
      have h := congrArg (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T v)
        (show sourceSoninProjection lambda +
            (ContinuousLinearMap.id ℂ finiteSCarrier -
              sourceSoninProjection lambda) =
          ContinuousLinearMap.id ℂ finiteSCarrier from by abel)
      simpa only [ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply] using h
    have h2 : sourceInclusion lambda ((sourceInclusion lambda).adjoint v) =
        sourceSoninProjection lambda v := by
      have h := congrArg (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T v)
        (sourceInclusion_comp_adjoint lambda)
      simpa only [ContinuousLinearMap.comp_apply] using h
    rw [h2]
    exact h1.symm
  have horth : inner ℂ (sourceInclusion lambda
      ((sourceInclusion lambda).adjoint v))
      ((ContinuousLinearMap.id ℂ finiteSCarrier -
        sourceSoninProjection lambda) v) = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hzero, inner_zero_right]
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (sourceInclusion lambda ((sourceInclusion lambda).adjoint v))
    ((ContinuousLinearMap.id ℂ finiteSCarrier -
      sourceSoninProjection lambda) v) horth
  conv_lhs => rw [hdecomp]
  rw [pow_two, hpyth, pow_two, pow_two, g8BridgeSourceInclusion_norm_map]

/-- Bridge fact B1 (map 042 §3): the survivor coframe is the Euler upper
factor times the source inclusion composed with the source-side Schur leg. -/
theorem g8MetricSurvivorCoframe_eq_smul_sourceInclusion_comp_survivorSourceLeg
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    g8MetricSurvivorCoframe lambda family =
      (finiteEulerUpperFactor family.visiblePrimes : ℂ) •
        (sourceInclusion lambda ∘L g8SurvivorSourceLeg lambda family) := by
  unfold g8MetricSurvivorCoframe g8SurvivorSourceLeg newSuffixFrame
    parameterizedSoninPolarFrame
    Source.CCM25Concrete.CCM24FiniteSFrameGramCalculus.parameterizedSoninFrame
    sourceInclusion
  rw [show parameterizedFiniteEulerFactor 1 [] =
      (ContinuousLinearMap.id ℂ finiteSCarrier) from by
        rw [parameterizedFiniteEulerFactor_one,
          ccm24FiniteEulerTransportEquiv_nil]
        rfl]
  simp only [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.id_comp]

set_option maxHeartbeats 1000000 in
-- reason: whnf timeout while unifying the large composed split terms
/-- Exact pointwise split of the survivor diagonal energy: the full norm
squared equals the Euler upper factor squared times the sum of the in-Sonin
response leg and the leakage-band leg, both evaluated after the source-side
Schur leg. -/
theorem g8SurvivorCoframe_normSq_pointwise_split
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily) (w : sourceSoninCarrier lambda) :
    ‖(rootConvolution owner ∘L g8MetricSurvivorCoframe lambda family) w‖ ^ 2 =
      (‖(finiteEulerUpperFactor family.visiblePrimes : ℂ)‖ : ℝ) ^ 2 *
        (‖((sourceInclusion lambda)† ∘L rootConvolution owner ∘L
            sourceInclusion lambda) (g8SurvivorSourceLeg lambda family w)‖ ^ 2 +
          ‖((ContinuousLinearMap.id ℂ finiteSCarrier -
            sourceSoninProjection lambda) ∘L rootConvolution owner ∘L
              sourceInclusion lambda) (g8SurvivorSourceLeg lambda family w)‖ ^ 2) := by
  rw [g8MetricSurvivorCoframe_eq_smul_sourceInclusion_comp_survivorSourceLeg,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.map_smul, norm_smul, mul_pow,
    ContinuousLinearMap.comp_apply]
  have hsplit := g8BridgeSoninCarrier_normSq_split lambda
    (rootConvolution owner (sourceInclusion lambda
      (g8SurvivorSourceLeg lambda family w)))
  rw [hsplit]
  simp only [ContinuousLinearMap.comp_apply]

/-- Real algebra behind the necessity direction: from the exact split, the
in-Sonin term is dominated by the inverse square times the full term. -/
private theorem invSquare_dominates_of_split {a b c u : ℝ}
    (hsplit : c = u ^ 2 * (a + b)) (hupos : 0 < u) (hb : 0 ≤ b) :
    a ≤ (u ^ 2)⁻¹ * c := by
  have h1 : a + b = (u ^ 2)⁻¹ * c := by
    rw [eq_inv_mul_iff_mul_eq₀ (by positivity : (u:ℝ) ^ 2 ≠ 0), hsplit]
  have h2 : a ≤ a + b := le_add_of_nonneg_right hb
  rw [h1] at h2
  exact h2

/-- The leakage-band leg of the survivor diagonal energy is square-summable
on every named source basis: it is the selected-root source-Sonin leakage
precomposed with the bounded source-side Schur leg. -/
theorem g8SurvivorSourceLeg_outLeg_normSq_summable_of_sourceSoninLeakage
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily)
    {ρ : Type*} (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) :
    Summable fun i : ρ =>
      ‖((ContinuousLinearMap.id ℂ finiteSCarrier -
        sourceSoninProjection lambda) ∘L rootConvolution owner ∘L
          sourceInclusion lambda) (g8SurvivorSourceLeg lambda family
            (sourceBasis i))‖ ^ 2 :=
  PositiveTrace.summable_normSq_precomp sourceBasis
    (survivorBridgeBasis finiteSCarrier) sourceBasis
    ((ContinuousLinearMap.id ℂ finiteSCarrier -
      sourceSoninProjection lambda) ∘L rootConvolution owner ∘L
        sourceInclusion lambda)
    (g8SurvivorSourceLeg lambda family)
    (selectedRoot_sourceSoninLeakage_sourceBasis_normSq_summable owner lambda
      sourceBasis)

/-- Necessity direction: the survivor coframe diagonal energy controls the
in-Sonin response leg on the source carrier. -/
theorem g8SurvivorSourceLeg_inLeg_normSq_summable_of_coframe_energy
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily)
    {ρ : Type*} (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (henergy : Summable fun i : ρ =>
      ‖(rootConvolution owner ∘L g8MetricSurvivorCoframe lambda family)
        (sourceBasis i)‖ ^ 2) :
    Summable fun i : ρ =>
      ‖((sourceInclusion lambda)† ∘L rootConvolution owner ∘L
        sourceInclusion lambda) (g8SurvivorSourceLeg lambda family
          (sourceBasis i))‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_)
    (henergy.mul_left
      (((‖(finiteEulerUpperFactor family.visiblePrimes : ℂ)‖ : ℝ) ^ 2)⁻¹))
  exact invSquare_dominates_of_split
    (g8SurvivorCoframe_normSq_pointwise_split owner lambda family
      (sourceBasis i))
    (by
      rw [Complex.norm_real]
      exact abs_pos.mpr
        (ne_of_gt (finiteEulerUpperFactor_pos family.visiblePrimes)))
    (sq_nonneg _)

set_option maxHeartbeats 1000000 in
-- reason: composed split terms in the congruence rewrite need extra budget
/-- Sufficiency direction: with the leakage-band leg already dominated, the
in-Sonin response leg on the source carrier reproduces the survivor coframe
diagonal energy. -/
theorem g8SurvivorCoframe_energy_summable_of_inLeg
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily)
    {ρ : Type*} (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hin : Summable fun i : ρ =>
      ‖((sourceInclusion lambda)† ∘L rootConvolution owner ∘L
        sourceInclusion lambda) (g8SurvivorSourceLeg lambda family
          (sourceBasis i))‖ ^ 2) :
    Summable fun i : ρ =>
      ‖(rootConvolution owner ∘L g8MetricSurvivorCoframe lambda family)
        (sourceBasis i)‖ ^ 2 := by
  have hout := g8SurvivorSourceLeg_outLeg_normSq_summable_of_sourceSoninLeakage
    owner lambda family sourceBasis
  have hadd := (hin.add hout).mul_left
    ((‖(finiteEulerUpperFactor family.visiblePrimes : ℂ)‖ : ℝ) ^ 2)
  exact Summable.congr hadd (fun i =>
    (g8SurvivorCoframe_normSq_pointwise_split owner lambda family
      (sourceBasis i)).symm)

/-- The G8 survivor diagonal energy obligation is exactly the in-Sonin
source-carrier square-sum after the source-side Schur leg: unconditional in
both directions, because the leakage-band leg is dominated by the committed
selected-root source-Sonin leakage square-sum. -/
theorem g8SurvivorCoframe_energy_iff_sourceCarrier_inLeg
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily)
    {ρ : Type*} (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) :
    (Summable fun i : ρ =>
      ‖(rootConvolution owner ∘L g8MetricSurvivorCoframe lambda family)
        (sourceBasis i)‖ ^ 2) ↔
    Summable fun i : ρ =>
      ‖((sourceInclusion lambda)† ∘L rootConvolution owner ∘L
        sourceInclusion lambda) (g8SurvivorSourceLeg lambda family
          (sourceBasis i))‖ ^ 2 :=
  ⟨fun h => g8SurvivorSourceLeg_inLeg_normSq_summable_of_coframe_energy owner
    lambda family sourceBasis h,
   fun h => g8SurvivorCoframe_energy_summable_of_inLeg owner lambda family
    sourceBasis h⟩

end Dev
end ConnesWeilRH
