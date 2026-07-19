/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkov
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSJuliaBessel

/-!
# Canonical Julia defects for the causal Euler input

The normalized one-prime inverse is a contraction, so its canonical defect
can be formed without a stored defect witness.  This module deliberately does
not identify the ambient inverse with Proof 351's sequential current-range
transfer.  That identification requires the actual graph pullback and stays
as a separate source obligation.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSJuliaCausal

open CCM24FiniteSCausalMarkov
open CCM24FiniteSJuliaBessel
open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSInverseMetric

open scoped InnerProduct

/-! One visible-prime square-function weight. -/
noncomputable def primeJuliaWeight (p : CCM24VisiblePrime) : ℝ :=
  (p : ℝ) - 1

theorem primeJuliaWeight_nonneg (p : CCM24VisiblePrime) :
    0 ≤ primeJuliaWeight p := by
  unfold primeJuliaWeight
  have hp : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Nat.le_of_lt p.property)
  linarith

/-! An isometric inclusion is contractive in operator norm. -/
theorem norm_le_one_of_isometric_inclusion
    {H K : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (inclusion : H →L[ℂ] K)
    (hinclusion : ∀ x : H, ‖inclusion x‖ = ‖x‖) :
    ‖inclusion‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  calc
    ‖inclusion x‖ = ‖x‖ := hinclusion x
    _ ≤ 1 * ‖x‖ := by simp

/-! Compression preserves the contraction bound when the carrier map is
isometric.  The proof uses the adjoint norm identity, so it does not assume
that an ambient projection is a unitary conjugation. -/
theorem compressedTransfer_norm_le_one
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (inclusion : H →L[ℂ] K) (ambientTransfer : K →L[ℂ] K)
    (hinclusion : ∀ x : H, ‖inclusion x‖ = ‖x‖)
    (hambient : ‖ambientTransfer‖ ≤ 1) :
    ‖inclusion† ∘L ambientTransfer ∘L inclusion‖ ≤ 1 := by
  have hinclusion_norm : ‖inclusion‖ ≤ 1 :=
    norm_le_one_of_isometric_inclusion inclusion hinclusion
  calc
    ‖inclusion† ∘L ambientTransfer ∘L inclusion‖ ≤
        ‖inclusion† ∘L ambientTransfer‖ * ‖inclusion‖ :=
      by
        simpa only [ContinuousLinearMap.comp_assoc] using
          (ContinuousLinearMap.opNorm_comp_le
            (inclusion† ∘L ambientTransfer) inclusion)
    _ ≤ (‖inclusion†‖ * ‖ambientTransfer‖) * ‖inclusion‖ := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = (‖inclusion‖ * ‖ambientTransfer‖) * ‖inclusion‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ (1 * 1) * 1 := by
      gcongr
    _ = 1 := by norm_num

/-! The converse contractivity readback used by the actual Schur carrier. -/
theorem norm_le_one_of_adjoint_comp_self_le_id
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (transfer : H →L[ℂ] H)
    (hcontract : transfer† ∘L transfer ≤ ContinuousLinearMap.id ℂ H) :
    ‖transfer‖ ≤ 1 := by
  have hgram_nonneg :
      (0 : H →L[ℂ] H) ≤ transfer† ∘L transfer :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      (ContinuousLinearMap.isPositive_adjoint_comp_self transfer)
  have hgram_norm : ‖transfer† ∘L transfer‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg
      (transfer† ∘L transfer) hgram_nonneg).mpr hcontract
  rw [ContinuousLinearMap.norm_adjoint_comp_self] at hgram_norm
  apply (sq_le_sq₀ (norm_nonneg transfer) (by norm_num)).mp
  nlinarith [hgram_norm]

/-!
The current-range version keeps the carrier change and the ambient transfer
visible in the same record.  In particular, the source transfer is not an
ambient inverse copied onto the fixed carrier: it is the compression

```text
F = J† Phi J.
```

The `currentRange` and `frame_range` fields make the range represented by `J`
part of the data.  The range-sine is likewise required to be the actual
ambient sine after applying `J`; a scalar Bessel majorant cannot be supplied
without that map.
-/
noncomputable def currentRangeCompressedTransfer
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (frame : H →L[ℂ] K) (ambientTransfer : K →L[ℂ] K) :
    H →L[ℂ] H :=
  frame† ∘L ambientTransfer ∘L frame

theorem currentRangeCompressedTransfer_norm_le_one
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (frame : H →L[ℂ] K) (ambientTransfer : K →L[ℂ] K)
    (hframe : ∀ x : H, ‖frame x‖ = ‖x‖)
    (hambient : ‖ambientTransfer‖ ≤ 1) :
    ‖currentRangeCompressedTransfer frame ambientTransfer‖ ≤ 1 := by
  exact compressedTransfer_norm_le_one frame ambientTransfer hframe hambient

noncomputable def currentRangeCompressedTransfer_contract
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (frame : H →L[ℂ] K) (ambientTransfer : K →L[ℂ] K)
    (hframe : ∀ x : H, ‖frame x‖ = ‖x‖)
    (hambient : ‖ambientTransfer‖ ≤ 1) :
    (currentRangeCompressedTransfer frame ambientTransfer)† ∘L
        currentRangeCompressedTransfer frame ambientTransfer ≤
      ContinuousLinearMap.id ℂ H := by
  exact adjoint_comp_self_le_id_of_norm_le_one
    (currentRangeCompressedTransfer frame ambientTransfer)
    (currentRangeCompressedTransfer_norm_le_one frame ambientTransfer
      hframe hambient)

/-!
The ambient defect is the larger defect after an isometric range pullback.
This is the operator form of the elementary estimate

```text
||D_Phi J x||^2 = ||J x||^2 - ||Phi J x||^2
                 <= ||x||^2 - ||J† Phi J x||^2
                 = ||D_(J† Phi J) x||^2.
```

A genuine range sine may therefore be controlled by an ambient Julia defect
only through this compression argument; a scalar norm witness is not enough.
-/
theorem canonicalJuliaDefect_comp_frame_normSq_le
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (frame : H →L[ℂ] K) (ambientTransfer : K →L[ℂ] K)
    (hframe : ∀ x : H, ‖frame x‖ = ‖x‖)
    (hambient : ‖ambientTransfer‖ ≤ 1) (x : H) :
    ‖canonicalJuliaDefect ambientTransfer
        (adjoint_comp_self_le_id_of_norm_le_one ambientTransfer hambient)
        (frame x)‖ ^ 2 ≤
    ‖canonicalJuliaDefect
          (currentRangeCompressedTransfer frame ambientTransfer)
          (currentRangeCompressedTransfer_contract frame ambientTransfer
            hframe hambient) x‖ ^ 2 := by
  have hframe_norm : ‖frame‖ ≤ 1 :=
    norm_le_one_of_isometric_inclusion frame hframe
  have hframe_adjoint_norm : ‖frame†‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hframe_norm
  have hcompressed_point :
      ‖currentRangeCompressedTransfer frame ambientTransfer x‖ ≤
        ‖ambientTransfer (frame x)‖ := by
    change ‖ContinuousLinearMap.adjoint frame
        (ambientTransfer (frame x))‖ ≤
      ‖ambientTransfer (frame x)‖
    calc
      ‖ContinuousLinearMap.adjoint frame
          (ambientTransfer (frame x))‖ ≤
          ‖frame†‖ * ‖ambientTransfer (frame x)‖ :=
        frame†.le_opNorm _
      _ ≤ 1 * ‖ambientTransfer (frame x)‖ :=
        mul_le_mul_of_nonneg_right hframe_adjoint_norm (norm_nonneg _)
      _ = ‖ambientTransfer (frame x)‖ := one_mul _
  have hcompressed_sq :
      ‖currentRangeCompressedTransfer frame ambientTransfer x‖ ^ 2 ≤
        ‖ambientTransfer (frame x)‖ ^ 2 := by
    nlinarith [mul_nonneg
      (sub_nonneg.mpr hcompressed_point)
      (add_nonneg
        (norm_nonneg (currentRangeCompressedTransfer frame ambientTransfer x))
        (norm_nonneg (ambientTransfer (frame x))))]
  have hambient_pythagorean :=
    canonicalJuliaDefect_pythagorean ambientTransfer
      (adjoint_comp_self_le_id_of_norm_le_one ambientTransfer hambient)
      (frame x)
  have hcompressed_pythagorean :=
    canonicalJuliaDefect_pythagorean
      (currentRangeCompressedTransfer frame ambientTransfer)
      (currentRangeCompressedTransfer_contract frame ambientTransfer
        hframe hambient) x
  have hframe_norm_eq := hframe x
  nlinarith [hcompressed_sq, norm_nonneg (ambientTransfer (frame x)),
    norm_nonneg (currentRangeCompressedTransfer frame ambientTransfer x),
    norm_nonneg (frame x), norm_nonneg x]

/-!
An actual current-range range-sine is obtained by factoring its weighted
column through the ambient canonical defect with a contraction.  This is the
direct Lean interface for the graph formula in Proof 351; the source-specific
fact left to prove is the factorization itself.
-/
structure FactorizedCurrentRangeJuliaStepData
    (H K G : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] where
  currentRange : ClosedSubmodule ℂ K
  frame : H →L[ℂ] K
  frame_isometry : ∀ x : H, ‖frame x‖ = ‖x‖
  frame_range : ∀ y : K, y ∈ currentRange ↔ ∃ x : H, frame x = y
  ambientTransfer : K →L[ℂ] K
  ambientTransfer_norm_le_one : ‖ambientTransfer‖ ≤ 1
  ambientRangeSine : K →L[ℂ] G
  weight : ℝ
  weight_nonneg : 0 ≤ weight
  ambientRangeSineFactor : K →L[ℂ] G
  ambientRangeSineFactor_norm_le_one : ‖ambientRangeSineFactor‖ ≤ 1
  weightedRangeSine_factorization :
    (Real.sqrt weight : ℂ) • ambientRangeSine =
      ambientRangeSineFactor ∘L
        canonicalJuliaDefect ambientTransfer
          (adjoint_comp_self_le_id_of_norm_le_one ambientTransfer
            ambientTransfer_norm_le_one)

structure CurrentRangeJuliaStepData
    (H K G : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] where
  currentRange : ClosedSubmodule ℂ K
  frame : H →L[ℂ] K
  frame_isometry : ∀ x : H, ‖frame x‖ = ‖x‖
  frame_range : ∀ y : K, y ∈ currentRange ↔ ∃ x : H, frame x = y
  ambientTransfer : K →L[ℂ] K
  ambientTransfer_norm_le_one : ‖ambientTransfer‖ ≤ 1
  ambientRangeSine : K →L[ℂ] G
  weight : ℝ
  weight_nonneg : 0 ≤ weight
  rangeSine_weighted_le : ∀ x : H,
    weight * ‖ambientRangeSine (frame x)‖ ^ 2 ≤
      ‖canonicalJuliaDefect
        (currentRangeCompressedTransfer frame ambientTransfer)
        (currentRangeCompressedTransfer_contract frame ambientTransfer
          frame_isometry ambientTransfer_norm_le_one) x‖ ^ 2

theorem weightedRangeSine_le_compressedDefect_of_factorization
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (frame : H →L[ℂ] K) (ambientTransfer : K →L[ℂ] K)
    (hframe : ∀ x : H, ‖frame x‖ = ‖x‖)
    (hambient : ‖ambientTransfer‖ ≤ 1)
    (ambientRangeSine : K →L[ℂ] G) (weight : ℝ)
    (hweight : 0 ≤ weight)
    (ambientRangeSineFactor : K →L[ℂ] G)
    (hfactor : ‖ambientRangeSineFactor‖ ≤ 1)
    (hfactorization :
      (Real.sqrt weight : ℂ) • ambientRangeSine =
        ambientRangeSineFactor ∘L
          canonicalJuliaDefect ambientTransfer
            (adjoint_comp_self_le_id_of_norm_le_one ambientTransfer hambient))
    (x : H) :
    weight * ‖ambientRangeSine (frame x)‖ ^ 2 ≤
      ‖canonicalJuliaDefect
          (currentRangeCompressedTransfer frame ambientTransfer)
          (currentRangeCompressedTransfer_contract frame ambientTransfer
            hframe hambient) x‖ ^ 2 := by
  have hfactor_point :
      ‖ambientRangeSineFactor
          (canonicalJuliaDefect ambientTransfer
            (adjoint_comp_self_le_id_of_norm_le_one ambientTransfer hambient)
            (frame x))‖ ≤
        ‖canonicalJuliaDefect ambientTransfer
          (adjoint_comp_self_le_id_of_norm_le_one ambientTransfer hambient)
          (frame x)‖ := by
    calc
      ‖ambientRangeSineFactor
          (canonicalJuliaDefect ambientTransfer
            (adjoint_comp_self_le_id_of_norm_le_one ambientTransfer hambient)
            (frame x))‖ ≤
          ‖ambientRangeSineFactor‖ *
            ‖canonicalJuliaDefect ambientTransfer
              (adjoint_comp_self_le_id_of_norm_le_one ambientTransfer hambient)
              (frame x)‖ := ambientRangeSineFactor.le_opNorm _
      _ ≤ 1 *
          ‖canonicalJuliaDefect ambientTransfer
            (adjoint_comp_self_le_id_of_norm_le_one ambientTransfer hambient)
            (frame x)‖ :=
        mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
      _ = _ := one_mul _
  have hfactorization_apply := congrArg
    (fun T : K →L[ℂ] G => T (frame x)) hfactorization
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
    at hfactorization_apply
  have hfactor_sq :
      ‖ambientRangeSineFactor
          (canonicalJuliaDefect ambientTransfer
            (adjoint_comp_self_le_id_of_norm_le_one ambientTransfer hambient)
            (frame x))‖ ^ 2 ≤
        ‖canonicalJuliaDefect ambientTransfer
          (adjoint_comp_self_le_id_of_norm_le_one ambientTransfer hambient)
          (frame x)‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hfactor_point)
      (add_nonneg
        (norm_nonneg (ambientRangeSineFactor
          (canonicalJuliaDefect ambientTransfer
            (adjoint_comp_self_le_id_of_norm_le_one ambientTransfer hambient)
            (frame x))))
        (norm_nonneg (canonicalJuliaDefect ambientTransfer
          (adjoint_comp_self_le_id_of_norm_le_one ambientTransfer hambient)
          (frame x))))]
  have hdefect_le := canonicalJuliaDefect_comp_frame_normSq_le frame
    ambientTransfer hframe hambient x
  have hsqrt :
      weight * ‖ambientRangeSine (frame x)‖ ^ 2 =
        ‖(Real.sqrt weight : ℂ) • ambientRangeSine (frame x)‖ ^ 2 := by
    rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hweight]
  calc
    weight * ‖ambientRangeSine (frame x)‖ ^ 2 =
        ‖(Real.sqrt weight : ℂ) • ambientRangeSine (frame x)‖ ^ 2 := hsqrt
    _ = ‖ambientRangeSineFactor
          (canonicalJuliaDefect ambientTransfer
            (adjoint_comp_self_le_id_of_norm_le_one ambientTransfer hambient)
            (frame x))‖ ^ 2 := by
      rw [hfactorization_apply]
    _ ≤ ‖canonicalJuliaDefect ambientTransfer
          (adjoint_comp_self_le_id_of_norm_le_one ambientTransfer hambient)
          (frame x)‖ ^ 2 := hfactor_sq
    _ ≤ ‖canonicalJuliaDefect
          (currentRangeCompressedTransfer frame ambientTransfer)
          (currentRangeCompressedTransfer_contract frame ambientTransfer
            hframe hambient) x‖ ^ 2 := hdefect_le

noncomputable def FactorizedCurrentRangeJuliaStepData.toCurrentRangeJuliaStepData
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (data : FactorizedCurrentRangeJuliaStepData H K G) :
    CurrentRangeJuliaStepData H K G :=
  { currentRange := data.currentRange
    frame := data.frame
    frame_isometry := data.frame_isometry
    frame_range := data.frame_range
    ambientTransfer := data.ambientTransfer
    ambientTransfer_norm_le_one := data.ambientTransfer_norm_le_one
    ambientRangeSine := data.ambientRangeSine
    weight := data.weight
    weight_nonneg := data.weight_nonneg
    rangeSine_weighted_le := by
      intro x
      exact weightedRangeSine_le_compressedDefect_of_factorization
        data.frame data.ambientTransfer data.frame_isometry
        data.ambientTransfer_norm_le_one data.ambientRangeSine data.weight
        data.weight_nonneg data.ambientRangeSineFactor
        data.ambientRangeSineFactor_norm_le_one
        data.weightedRangeSine_factorization x }

@[simp]
theorem FactorizedCurrentRangeJuliaStepData.toCurrentRangeJuliaStepData_frame
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (data : FactorizedCurrentRangeJuliaStepData H K G) :
    data.toCurrentRangeJuliaStepData.frame = data.frame :=
  rfl

@[simp]
theorem FactorizedCurrentRangeJuliaStepData.toCurrentRangeJuliaStepData_ambientRangeSine
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (data : FactorizedCurrentRangeJuliaStepData H K G) :
    data.toCurrentRangeJuliaStepData.ambientRangeSine =
      data.ambientRangeSine :=
  rfl

theorem CurrentRangeJuliaStepData.frame_mem_currentRange
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (data : CurrentRangeJuliaStepData H K G) (x : H) :
    data.frame x ∈ data.currentRange := by
  exact (data.frame_range (data.frame x)).mpr ⟨x, rfl⟩

theorem CurrentRangeJuliaStepData.exists_frame_of_mem_currentRange
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (data : CurrentRangeJuliaStepData H K G) {y : K}
    (hy : y ∈ data.currentRange) :
    ∃ x : H, data.frame x = y := by
  exact (data.frame_range y).mp hy

noncomputable def CurrentRangeJuliaStepData.toCanonicalJuliaStepData
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (data : CurrentRangeJuliaStepData H K G) :
    CanonicalJuliaStepData H G :=
  { transfer := currentRangeCompressedTransfer data.frame
      data.ambientTransfer
    rangeSine := data.ambientRangeSine ∘L data.frame
    weight := data.weight
    weight_nonneg := data.weight_nonneg
    transfer_contract := currentRangeCompressedTransfer_contract data.frame
      data.ambientTransfer data.frame_isometry
      data.ambientTransfer_norm_le_one
    rangeSine_weighted_le := by
      intro x
      simpa only [ContinuousLinearMap.comp_apply] using
        data.rangeSine_weighted_le x }

noncomputable def CurrentRangeJuliaStepData.toJuliaDefectStep
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (data : CurrentRangeJuliaStepData H K G) :
    JuliaDefectStep H G :=
  data.toCanonicalJuliaStepData.toJuliaDefectStep

@[simp]
theorem CurrentRangeJuliaStepData.toJuliaDefectStep_transfer
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (data : CurrentRangeJuliaStepData H K G) :
    data.toJuliaDefectStep.transfer =
      currentRangeCompressedTransfer data.frame data.ambientTransfer := by
  rfl

@[simp]
theorem CurrentRangeJuliaStepData.toJuliaDefectStep_rangeSine
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (data : CurrentRangeJuliaStepData H K G) :
    data.toJuliaDefectStep.rangeSine =
      data.ambientRangeSine ∘L data.frame := by
  rfl

/-! A list of these steps is the actual fixed-source Julia cascade. -/
noncomputable def currentRangeJuliaSteps
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (CurrentRangeJuliaStepData H K G)) :
    List (JuliaDefectStep H G) :=
  steps.map CurrentRangeJuliaStepData.toJuliaDefectStep

/-! The factorized form is the preferred source-facing constructor. -/
noncomputable def factorizedCurrentRangeJuliaSteps
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (FactorizedCurrentRangeJuliaStepData H K G)) :
    List (JuliaDefectStep H G) :=
  steps.map (fun data => data.toCurrentRangeJuliaStepData.toJuliaDefectStep)

theorem factorizedCurrentRangeJuliaSteps_eq_currentRangeJuliaSteps
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (steps : List (FactorizedCurrentRangeJuliaStepData H K G)) :
    factorizedCurrentRangeJuliaSteps steps =
      currentRangeJuliaSteps
        (steps.map FactorizedCurrentRangeJuliaStepData.toCurrentRangeJuliaStepData) := by
  simp only [factorizedCurrentRangeJuliaSteps, currentRangeJuliaSteps,
    List.map_map, Function.comp_def]

@[simp]
theorem factorizedCurrentRangeJuliaSteps_nil
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] :
    factorizedCurrentRangeJuliaSteps
      ([] : List (FactorizedCurrentRangeJuliaStepData H K G)) = [] :=
  rfl

@[simp]
theorem factorizedCurrentRangeJuliaSteps_cons
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (step : FactorizedCurrentRangeJuliaStepData H K G)
    (steps : List (FactorizedCurrentRangeJuliaStepData H K G)) :
    factorizedCurrentRangeJuliaSteps (step :: steps) =
      step.toCurrentRangeJuliaStepData.toJuliaDefectStep ::
        factorizedCurrentRangeJuliaSteps steps :=
  rfl

@[simp]
theorem currentRangeJuliaSteps_nil
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] :
    currentRangeJuliaSteps ([] : List (CurrentRangeJuliaStepData H K G)) = [] :=
  rfl

@[simp]
theorem currentRangeJuliaSteps_cons
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (step : CurrentRangeJuliaStepData H K G)
    (steps : List (CurrentRangeJuliaStepData H K G)) :
    currentRangeJuliaSteps (step :: steps) =
      step.toJuliaDefectStep :: currentRangeJuliaSteps steps :=
  rfl

/-!
This is the exact causal one-prime input before the current-range graph
pullback.  The only source-specific field is the square-gain inequality for
the supplied range-sine map.
-/
noncomputable def normalizedPrimeEulerCanonicalJuliaStepData
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (p : CCM24VisiblePrime) (rangeSine : finiteSCarrier →L[ℂ] G)
    (hrange : ∀ x : finiteSCarrier,
      primeJuliaWeight p * ‖rangeSine x‖ ^ 2 ≤
        ‖canonicalJuliaDefect
          (normalizedPrimeEulerInverse p)
          (adjoint_comp_self_le_id_of_norm_le_one
            (normalizedPrimeEulerInverse p)
            (norm_normalizedPrimeEulerInverse_le_one p)) x‖ ^ 2) :
    CanonicalJuliaStepData finiteSCarrier G := by
  let hcontract :
      (normalizedPrimeEulerInverse p)† ∘L
          normalizedPrimeEulerInverse p ≤
        ContinuousLinearMap.id ℂ finiteSCarrier :=
    adjoint_comp_self_le_id_of_norm_le_one
      (normalizedPrimeEulerInverse p)
      (norm_normalizedPrimeEulerInverse_le_one p)
  refine
    { transfer := normalizedPrimeEulerInverse p
      rangeSine := rangeSine
      weight := primeJuliaWeight p
      weight_nonneg := primeJuliaWeight_nonneg p
      transfer_contract := hcontract
      rangeSine_weighted_le := ?_ }
  simpa only [hcontract] using hrange

noncomputable def normalizedPrimeEulerCanonicalJuliaStep
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (p : CCM24VisiblePrime) (rangeSine : finiteSCarrier →L[ℂ] G)
    (hrange : ∀ x : finiteSCarrier,
      primeJuliaWeight p * ‖rangeSine x‖ ^ 2 ≤
        ‖canonicalJuliaDefect
          (normalizedPrimeEulerInverse p)
          (adjoint_comp_self_le_id_of_norm_le_one
            (normalizedPrimeEulerInverse p)
            (norm_normalizedPrimeEulerInverse_le_one p)) x‖ ^ 2) :
    JuliaDefectStep finiteSCarrier G :=
  (normalizedPrimeEulerCanonicalJuliaStepData p rangeSine hrange).toJuliaDefectStep

@[simp]
theorem normalizedPrimeEulerCanonicalJuliaStep_transfer
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (p : CCM24VisiblePrime) (rangeSine : finiteSCarrier →L[ℂ] G)
    (hrange : ∀ x : finiteSCarrier,
      primeJuliaWeight p * ‖rangeSine x‖ ^ 2 ≤
        ‖canonicalJuliaDefect
          (normalizedPrimeEulerInverse p)
          (adjoint_comp_self_le_id_of_norm_le_one
            (normalizedPrimeEulerInverse p)
            (norm_normalizedPrimeEulerInverse_le_one p)) x‖ ^ 2) :
    (normalizedPrimeEulerCanonicalJuliaStep p rangeSine hrange).transfer =
      normalizedPrimeEulerInverse p := by
  rfl

end CCM24FiniteSJuliaCausal
end CCM25Concrete
end Source
end ConnesWeilRH
