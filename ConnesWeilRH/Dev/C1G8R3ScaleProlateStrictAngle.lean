/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ScaleStrictAngle

/-!
# Strict angle for the moving-scale relative prolate factor

The compact-window Hardy compression controls the actual relative prolate
factor after moving both support projections to one carrier.  The proof uses
the inverse of `1 - C_b^2` to reconstruct vectors in the support complement
from their Hardy leakage.  It proves an angle gap, not positivity of the
detector's Weil quadratic form.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment
open Source.CCM25Concrete.CCM24UnitScaleProlateTraceReduction
open Source.CC20Concrete.ProlateTraceReduction
open Source.CC20Concrete.PositiveTrace

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier
local notation "Op" => Carrier →L[ℂ] Carrier

theorem doubledShiftHardyTranslationEquiv_involutive (b : ℝ) :
    Function.Involutive (doubledShiftHardyTranslationEquiv b) := by
  intro x
  have hsymm := doubledShiftHardyTranslationEquiv_symm_apply b
    (doubledShiftHardyTranslationEquiv b x)
  rw [(doubledShiftHardyTranslationEquiv b).symm_apply_apply] at hsymm
  have hcoerce : doubledShiftHardy b
      (doubledShiftHardyTranslationEquiv b x) =
        doubledShiftHardyTranslationEquiv b
          (doubledShiftHardyTranslationEquiv b x) := by
    have h := congrArg (fun T : Op => T
      (doubledShiftHardyTranslationEquiv b x))
      (doubledShiftHardyTranslationEquiv_eq b).symm
    simpa only [ContinuousLinearMap.coe_coe] using h
  exact hcoerce.symm.trans hsymm.symm

theorem doubledShiftHardyInteriorCompression_norm_eq_evenAdditive
    (b : ℝ) :
    ‖doubledShiftHardyInteriorCompression b‖ =
      ‖doubledShiftEvenAdditiveInteriorCompression b‖ := by
  rw [doubledShiftHardyInteriorCompression_eq_evenAdditiveConjugation]
  calc
    ‖ccm24EvenLogCarrierEquiv.toContinuousLinearEquiv.toContinuousLinearMap
        ∘L doubledShiftEvenAdditiveInteriorCompression b ∘L
          ccm24EvenLogCarrierEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap‖ =
        ‖doubledShiftEvenAdditiveInteriorCompression b ∘L
          ccm24EvenLogCarrierEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap‖ :=
        ccm24EvenLogCarrierEquiv.toLinearIsometry.norm_toContinuousLinearMap_comp
    _ = ‖doubledShiftEvenAdditiveInteriorCompression b‖ :=
      ContinuousLinearMap.opNorm_comp_linearIsometryEquiv
        (doubledShiftEvenAdditiveInteriorCompression b)
        ccm24EvenLogCarrierEquiv.symm

theorem doubledShiftHardyInteriorCompression_norm_lt_one
    (b : ℝ) : ‖doubledShiftHardyInteriorCompression b‖ < 1 := by
  rw [doubledShiftHardyInteriorCompression_norm_eq_evenAdditive]
  exact doubledShiftEvenAdditiveInteriorCompression_norm_lt_one b

set_option maxHeartbeats 800000 in
-- The inverse-complement reconstruction expands several nested projection identities.
theorem doubledShiftHardyStandardProlateFactor_norm_lt_one
    (b : ℝ) :
    ‖prolateFactor (doubledShiftHardyTranslationEquiv b)‖ < 1 := by
  let Ueq := doubledShiftHardyTranslationEquiv b
  let U : Op := Ueq
  let P : Op := cc20PositiveHalfLineProjection
  let M : Op := ContinuousLinearMap.id ℂ Carrier - P
  let R : Op := cc20TransportedSoninProjection Ueq
  let Q : Op := cc20TransportedHalfLineProjection Ueq
  let B : Op := supportComplementProjection Ueq
  let C : Op := M ∘L U ∘L M
  let L : Op := M ∘L U ∘L B
  let Ladj : Op := B ∘L U ∘L M
  let A : Op := ContinuousLinearMap.id ℂ Carrier - C ∘L C
  have hU (x : Carrier) : Ueq (Ueq x) = x :=
    doubledShiftHardyTranslationEquiv_involutive b x
  have hU2 : U ∘L U = ContinuousLinearMap.id ℂ Carrier := by
    apply ContinuousLinearMap.ext
    intro x
    exact hU x
  have hU2point (x : Carrier) : U (U x) = x := by
    have h := congrArg (fun T : Op => T x) hU2
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using h
  have hUself : IsSelfAdjoint U := by
    apply LinearMap.IsSymmetric.isSelfAdjoint
    intro x y
    calc
      inner ℂ (U x) y = inner ℂ (Ueq x) (Ueq (Ueq y)) := by
        exact congrArg (fun z : Carrier => inner ℂ (Ueq x) z)
          (hU y).symm
      _ = inner ℂ x (U y) := Ueq.inner_map_map x (Ueq y)
  have hUeqSymm (x : Carrier) : Ueq.symm x = Ueq x := by
    apply Ueq.injective
    calc
      Ueq (Ueq.symm x) = x := Ueq.apply_symm_apply x
      _ = Ueq (Ueq x) := (hU x).symm
  have hQ : Q = U ∘L P ∘L U := by
    apply ContinuousLinearMap.ext
    intro x
    dsimp [Q, P, U]
    rw [cc20TransportedHalfLineProjection_apply]
    exact hUeqSymm _
  have hQpoint (x : Carrier) :
      Q x = Ueq.symm (P (Ueq x)) := by
    change cc20TransportedHalfLineProjection Ueq x =
      Ueq.symm (cc20PositiveHalfLineProjection (Ueq x))
    exact cc20TransportedHalfLineProjection_apply Ueq x
  have hP2 : P ∘L P = P := by
    dsimp [P]
    exact cc20PositiveHalfLineProjection_isIdempotentElem
  have hR2 : R ∘L R = R := by
    dsimp [R]
    exact (cc20TransportedSoninProjection_isStarProjection Ueq).isIdempotentElem
  have hPR : P ∘L R = R := by
    dsimp [P, R]
    exact cc20PositiveHalfLineProjection_comp_sonin Ueq
  have hRP : R ∘L P = R := by
    dsimp [P, R]
    exact cc20TransportedSonin_comp_positiveHalfLineProjection Ueq
  have hQR : Q ∘L R = R := by
    dsimp [Q, R]
    exact cc20TransportedHalfLineProjection_comp_sonin Ueq
  have hM2 : M ∘L M = M := by
    dsimp [M, P]
    exact unitInteriorSupportProjection_isIdempotentElem
  have hM2point (x : Carrier) : M (M x) = M x := by
    have h := congrArg (fun T : Op => T x) hM2
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hPdecomp : P =
      ContinuousLinearMap.id ℂ Carrier - M := by
    dsimp [P, M]
    noncomm_ring
  have hMself : IsSelfAdjoint M := by
    dsimp [M, P]
    exact (IsSelfAdjoint.one (Carrier →L[ℂ] Carrier)).sub
      cc20PositiveHalfLineProjection_isSelfAdjoint
  have hB2 : B ∘L B = B := by
    dsimp [B]
    exact supportComplementProjection_isIdempotentElem Ueq
  have hB2point (x : Carrier) : B (B x) = B x := by
    have h := congrArg (fun T : Op => T x) hB2
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hBself : IsSelfAdjoint B := by
    dsimp [B]
    exact supportComplementProjection_isSelfAdjoint Ueq
  have hPB : P ∘L B = B := by
    change P ∘L (P - R) = P - R
    calc
      P ∘L (P - R) = P ∘L P - P ∘L R := by
        rw [ContinuousLinearMap.comp_sub]
      _ = P - R := by rw [hP2, hPR]
  have hRB : R ∘L B = 0 := by
    change R ∘L (P - R) = 0
    rw [ContinuousLinearMap.comp_sub, hRP, hR2]
    exact sub_self _
  have hMURzero : M ∘L U ∘L R = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    have hQRx := congrArg (fun T : Op => T x) hQR
    have hQRpoint : Ueq.symm (P (Ueq (R x))) = R x := by
      calc
        Ueq.symm (P (Ueq (R x))) = Q (R x) := (hQpoint (R x)).symm
        _ = R x := by simpa only [ContinuousLinearMap.comp_apply] using hQRx
    have hPfixed : P (U (R x)) = U (R x) := by
      have h := congrArg Ueq hQRpoint
      simpa only [Ueq.apply_symm_apply] using h
    change U (R x) - P (U (R x)) = 0
    rw [hPfixed, sub_self]
  have hCcompression : C = doubledShiftHardyInteriorCompression b := by
    dsimp [C, M, P, U]
    rw [doubledShiftHardyTranslationEquiv_eq]
    rfl
  have hCnorm : ‖C‖ < 1 := by
    calc
      ‖C‖ = ‖doubledShiftHardyInteriorCompression b‖ :=
        congrArg norm hCcompression
      _ < 1 := doubledShiftHardyInteriorCompression_norm_lt_one b
  have hCMpoint (x : Carrier) : C (M x) = C x := by
    change M (U (M (M x))) = M (U (M x))
    rw [hM2point]
  have hMCpoint (x : Carrier) : M (C x) = C x := by
    change M (M (U (M x))) = M (U (M x))
    rw [hM2point]
  have hCM : C ∘L M = C := by
    apply ContinuousLinearMap.ext
    intro x
    simpa only [ContinuousLinearMap.comp_apply] using hCMpoint x
  have hMC : M ∘L C = C := by
    apply ContinuousLinearMap.ext
    intro x
    simpa only [ContinuousLinearMap.comp_apply] using hMCpoint x
  have hCCnorm : ‖C ∘L C‖ < 1 := by
    calc
      ‖C ∘L C‖ ≤ ‖C‖ ^ 2 := by
        simpa [pow_two] using norm_mul_le C C
      _ < 1 := by nlinarith [hCnorm, norm_nonneg C]
  have hAunit : IsUnit A := by
    dsimp [A]
    exact isUnit_one_sub_of_norm_lt_one hCCnorm
  let Ainv : Op := Ring.inverse A
  have hAinvRight : A ∘L Ainv = ContinuousLinearMap.id ℂ Carrier := by
    dsimp [Ainv]
    exact Ring.mul_inverse_cancel _ hAunit
  have hAinvLeft : Ainv ∘L A = ContinuousLinearMap.id ℂ Carrier := by
    dsimp [Ainv]
    exact Ring.inverse_mul_cancel _ hAunit
  have hAcommM : A ∘L M = M ∘L A := by
    apply ContinuousLinearMap.ext
    intro x
    dsimp [A]
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub]
    rw [hCMpoint x, hMCpoint (C x)]
  have hAinvRightPoint (x : Carrier) : A (Ainv x) = x := by
    have h := congrArg (fun T : Op => T x) hAinvRight
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using h
  have hAinvLeftPoint (x : Carrier) : Ainv (A x) = x := by
    have h := congrArg (fun T : Op => T x) hAinvLeft
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using h
  have hAinj : Function.Injective A := by
    intro x y hxy
    calc
      x = Ainv (A x) := (hAinvLeftPoint x).symm
      _ = Ainv (A y) := congrArg Ainv hxy
      _ = y := hAinvLeftPoint y
  have hAinvPreservesM (x : Carrier) (hx : M x = x) :
      M (Ainv x) = Ainv x := by
    apply hAinj
    calc
      A (M (Ainv x)) = M (A (Ainv x)) := by
        have h := congrArg (fun T : Op => T (Ainv x)) hAcommM
        simpa only [ContinuousLinearMap.comp_apply] using h
      _ = M x := by rw [hAinvRightPoint]
      _ = x := hx
      _ = A (Ainv x) := (hAinvRightPoint x).symm
  have hLadj : L.adjoint = Ladj := by
    dsimp [L, Ladj]
    rw [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_comp,
      hBself.adjoint_eq, hUself.adjoint_eq, hMself.adjoint_eq,
      ContinuousLinearMap.comp_assoc]
  have hC_apply (x : Carrier) : C x = M (U (M x)) := rfl
  have hC_square_apply (x : Carrier) :
      C (C x) = M (U (M (U (M x)))) := by
    calc
      C (C x) = M (U (M (C x))) := hC_apply (C x)
      _ = M (U (C x)) := by rw [hMCpoint]
      _ = M (U (M (U (M x)))) := by rw [hC_apply x]
  have hLLadj (x : Carrier) : L (Ladj x) = M x - C (C x) := by
    change M (U (B (B (U (M x))))) = M x - C (C x)
    rw [hB2point]
    have hPdecompPoint (z : Carrier) : P z = z - M z := by
      have h := congrArg (fun T : Op => T z) hPdecomp
      simpa only [ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.id_apply] using h
    have hMURzeroPoint (z : Carrier) : M (U (R z)) = 0 := by
      have h := congrArg (fun T : Op => T z) hMURzero
      simpa only [ContinuousLinearMap.comp_apply] using h
    rw [show B (U (M x)) =
        P (U (M x)) - R (U (M x)) by rfl]
    simp only [map_sub]
    rw [hMURzeroPoint]
    simp only [sub_zero]
    rw [hPdecompPoint]
    simp only [map_sub]
    rw [hU2point, hM2point, hC_square_apply]
  have hLCrange (x : Carrier) : M (L x) = L x := by
    change M (M (U (B x))) = M (U (B x))
    rw [hM2point]
  have hBRangeAdj (x : Carrier) : B (Ladj x) = Ladj x := by
    change B (B (U (M x))) = B (U (M x))
    rw [hB2point]
  have hLzero (x : Carrier) (hBx : B x = x) (hLx : L x = 0) :
      x = 0 := by
    have hPBx (y : Carrier) : P (B y) = B y := by
      have h := congrArg (fun T : Op => T y) hPB
      simpa only [ContinuousLinearMap.comp_apply] using h
    have hRBx (y : Carrier) : R (B y) = 0 := by
      have h := congrArg (fun T : Op => T y) hRB
      simpa only [ContinuousLinearMap.comp_apply] using h
    have hPx : P x = x := by
      calc
        P x = P (B x) := congrArg P hBx.symm
        _ = B x := hPBx x
        _ = x := hBx
    have hRxZero : R x = 0 := by
      calc
        R x = R (B x) := congrArg R hBx.symm
        _ = 0 := hRBx x
    have hPUx : P (U x) = U x := by
      unfold L at hLx
      simp only [ContinuousLinearMap.comp_apply, hBx] at hLx
      change U x - P (U x) = 0 at hLx
      exact (sub_eq_zero.mp hLx).symm
    have hQx : Q x = x := by
      have h := congrArg (fun T : Op => T x) hQ
      calc
        Q x = U (P (U x)) := by
          simpa only [ContinuousLinearMap.comp_apply] using h
        _ = U (U x) := congrArg U hPUx
        _ = x := hU x
    have hmemP : x ∈ cc20PositiveHalfLineClosedRange := by
      change x ∈ P.range
      exact (mem_range_iff_of_isIdempotentElem P
        cc20PositiveHalfLineProjection_isIdempotentElem x).2 hPx
    have hmemQ : x ∈ cc20TransportedHalfLineClosedRange Ueq := by
      change x ∈ Q.range
      exact (mem_range_iff_of_isIdempotentElem Q
        (cc20TransportedHalfLineProjection_isIdempotentElem Ueq) x).2 hQx
    have hRx : R x = x := by
      exact Submodule.starProjection_eq_self_iff.mpr
        ⟨hmemP, hmemQ⟩
    rw [hRxZero] at hRx
    exact hRx.symm
  have hReconstruction (x : Carrier) (hBx : B x = x) :
      Ladj (Ainv (L x)) = x := by
    let z := Ainv (L x)
    have hLxM : M (L x) = L x := hLCrange x
    have hzM : M z = z := hAinvPreservesM (L x) hLxM
    have hAz : A z = L x := hAinvRightPoint (L x)
    have hGramAt' : L (Ladj z) = M z - C (C z) := by
      exact hLLadj z
    have hLsame : L (Ladj z) = L x := by
      calc
        L (Ladj z) = M z - C (C z) := hGramAt'
        _ = A z := by
          dsimp [A]
          rw [hzM]
        _ = L x := hAz
    have hBz : B (Ladj z) = Ladj z := by
      exact hBRangeAdj z
    let d := Ladj z - x
    have hdB : B d = d := by
      dsimp [d]
      rw [map_sub, hBz, hBx]
    have hdL : L d = 0 := by
      dsimp [d]
      rw [map_sub, hLsame, sub_self]
    have hdZero := hLzero d hdB hdL
    exact sub_eq_zero.mp hdZero
  let K : ℝ := max 1 (‖Ladj‖ * ‖Ainv‖)
  have hKone : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hKone
  have hreconstructionBound (x : Carrier) (hBx : B x = x) :
      ‖x‖ ≤ K * ‖L x‖ := by
    calc
      ‖x‖ = ‖Ladj (Ainv (L x))‖ := congrArg norm (hReconstruction x hBx).symm
      _ ≤ ‖Ladj‖ * ‖Ainv (L x)‖ := Ladj.le_opNorm _
      _ ≤ ‖Ladj‖ * (‖Ainv‖ * ‖L x‖) := by
        gcongr
        exact Ainv.le_opNorm _
      _ = (‖Ladj‖ * ‖Ainv‖) * ‖L x‖ := by ring
      _ ≤ K * ‖L x‖ := by
        gcongr
        exact le_max_right _ _
  let delta : ℝ := K⁻¹
  have hdeltaPos : 0 < delta := inv_pos.mpr hKpos
  have hdeltaLe : delta ≤ 1 := by
    dsimp [delta]
    exact inv_le_one_of_one_le₀ hKone
  have hdeltaLeakage (x : Carrier) (hBx : B x = x) :
      delta * ‖x‖ ≤ ‖L x‖ := by
    have hbound := hreconstructionBound x hBx
    dsimp [delta]
    rw [inv_mul_le_iff₀ hKpos]
    simpa [mul_assoc] using hbound
  have hLcompB (x : Carrier) : L (B x) = L x := by
    change M (U (B (B x))) = M (U (B x))
    rw [hB2point]
  have hBnorm (x : Carrier) : ‖B x‖ ≤ ‖x‖ := by
    calc
      ‖B x‖ ≤ ‖B‖ * ‖x‖ := B.le_opNorm x
      _ ≤ 1 * ‖x‖ := by
        gcongr
        exact (supportComplementProjection_isStarProjection Ueq).norm_le
      _ = ‖x‖ := one_mul _
  have hpythagorean (x : Carrier) :
      ‖prolateFactor Ueq x‖ ^ 2 + ‖L x‖ ^ 2 = ‖B x‖ ^ 2 := by
    let y := U (B x)
    have hpyth := cc20PositiveHalfLineClosedRange.toSubmodule
      |>.norm_sq_eq_add_norm_sq_starProjection y
    rw [← cc20PositiveHalfLineProjection_eq_starProjection] at hpyth
    rw [Submodule.starProjection_orthogonal,
      ← cc20PositiveHalfLineProjection_eq_starProjection] at hpyth
    have hyNorm : ‖y‖ = ‖B x‖ := by
      dsimp [y, U]
      exact Ueq.norm_map _
    have hfactorNorm : ‖prolateFactor Ueq x‖ =
        ‖cc20PositiveHalfLineProjection y‖ := by
      change ‖Q (B x)‖ = _
      rw [cc20TransportedHalfLineProjection_apply Ueq (B x)]
      exact Ueq.symm.norm_map _
    have hleakage : L x =
        (ContinuousLinearMap.id ℂ Carrier -
          cc20PositiveHalfLineProjection) y := by
      rfl
    rw [hfactorNorm, hleakage, ← hyNorm]
    exact hpyth.symm
  let theta : ℝ := Real.sqrt (1 - delta ^ 2)
  have hthetaNonneg : 0 ≤ theta := Real.sqrt_nonneg _
  have hinside : 0 ≤ 1 - delta ^ 2 := by
    nlinarith [hdeltaPos, hdeltaLe]
  have hthetaLtOne : theta < 1 := by
    have hsqrt := Real.sq_sqrt hinside
    dsimp [theta] at hsqrt hthetaNonneg ⊢
    nlinarith [hdeltaPos]
  have hfactorApply (x : Carrier) :
      ‖prolateFactor Ueq x‖ ≤ theta * ‖x‖ := by
    let y := B x
    have hyB : B y = y := by
      dsimp [y]
      exact congrArg (fun T : Op => T x) hB2
    have hlower := hdeltaLeakage y hyB
    have hleakageSame : L y = L x := by
      dsimp [y]
      exact hLcompB x
    rw [hleakageSame] at hlower
    have hpyth := hpythagorean x
    have hlowerSq : (delta * ‖y‖) ^ 2 ≤ ‖L x‖ ^ 2 := by
      exact (sq_le_sq₀
        (mul_nonneg hdeltaPos.le (norm_nonneg _)) (norm_nonneg _)).2 hlower
    have hyNormSq : ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (hBnorm x)
    have hangleSq : ‖prolateFactor Ueq x‖ ^ 2 ≤
        (1 - delta ^ 2) * ‖x‖ ^ 2 := by
      dsimp only [y] at hpyth hlowerSq hyNormSq ⊢
      nlinarith
    have hsqrt := Real.sq_sqrt hinside
    have hrightNonneg : 0 ≤ theta * ‖x‖ :=
      mul_nonneg hthetaNonneg (norm_nonneg _)
    apply (sq_le_sq₀ (norm_nonneg _) hrightNonneg).mp
    dsimp [theta]
    nlinarith
  have hfactorNorm : ‖prolateFactor Ueq‖ ≤ theta := by
    apply ContinuousLinearMap.opNorm_le_bound _ hthetaNonneg
    intro x
    exact hfactorApply x
  exact lt_of_le_of_lt hfactorNorm hthetaLtOne

theorem doubledShiftProlateHilbertSchmidtFactor_norm_lt_one
    (b : ℝ) : ‖doubledShiftProlateHilbertSchmidtFactor b‖ < 1 := by
  rw [doubledShiftProlateHilbertSchmidtFactor_norm_eq_standard]
  exact doubledShiftHardyStandardProlateFactor_norm_lt_one b

theorem doubledShiftProlateHilbertSchmidtFactor_summable
    {ι : Type*} (basis : HilbertBasis ι ℂ Carrier) (b : ℝ) :
    Summable fun i =>
      ‖doubledShiftProlateHilbertSchmidtFactor b (basis i)‖ ^ 2 := by
  exact doubledShiftProlateHilbertSchmidtFactor_summable_of_strictAngle_and_interiorCompression
    basis b (doubledShiftProlateHilbertSchmidtFactor_norm_lt_one b)
    (doubledShiftHardyInteriorCompression_summable basis b)

theorem doubledShiftProlatePositiveComposition_isTraceClassAlong
    {ι : Type*} (basis : HilbertBasis ι ℂ Carrier) (b : ℝ) :
    IsTraceClassAlong basis
      ((doubledShiftProlateHilbertSchmidtFactor b).adjoint ∘L
        doubledShiftProlateHilbertSchmidtFactor b) := by
  let data : Source.CC20Concrete.PositiveTrace.BasisHilbertSchmidtData basis :=
    { operator := doubledShiftProlateHilbertSchmidtFactor b
      summable_normSq :=
        doubledShiftProlateHilbertSchmidtFactor_summable basis b }
  exact data.positiveComposition_isTraceClassAlong

end Dev
end ConnesWeilRH
