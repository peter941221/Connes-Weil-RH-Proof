/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ProlateRelativeNormalForm
import ConnesWeilRH.Dev.C1G8R3DoubledShiftNormalForm
import ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScaleProlateTraceReduction

/-!
# R3 relative defect and the shifted raw crossing

The relative prolate factor is the source Fourier projection applied to the
part of the doubled-shift radial projection outside the genuine intersection.
This leaf proves the exact defect cancellation for that factor.  After the
radial coordinate is translated back to the fixed positive half-line, the
remaining raw crossing is governed by the involution

`K_b = T_(2*b) H`.

No Hilbert--Schmidt estimate is inserted here.  The point of the normal form
is to make the next analytic obligation a compact-window kernel statement for
the explicit shifted involution.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment
open Source.CCM25Concrete.CCM24UnitScaleProlateTraceReduction
open Source.CCM25Concrete.SelectedCrossingOperatorBridge
open Source.C1SemilocalHardyTitchmarshUnitarityReduction

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier
local notation "Op" => Carrier →L[ℂ] Carrier

noncomputable def doubledShiftProlateDefectFactor (b : ℝ) : Op :=
  (ContinuousLinearMap.id ℂ Carrier -
      (doubledShiftRadialProjection b -
        doubledShiftSoninIntersectionProjection b)) ∘L
    doubledShiftProlateHilbertSchmidtFactor b

noncomputable def doubledShiftRawSupportCrossing (b : ℝ) : Op :=
  (ContinuousLinearMap.id ℂ Carrier - doubledShiftRadialProjection b) ∘L
    sourceFourierSupportProjection unitSoninScale ∘L
      doubledShiftRadialProjection b

noncomputable def doubledShiftHardyRawSupportCrossing (b : ℝ) : Op :=
  (ContinuousLinearMap.id ℂ Carrier - cc20PositiveHalfLineProjection) ∘L
    doubledShiftHardy b ∘L cc20PositiveHalfLineProjection ∘L
      doubledShiftHardy b ∘L cc20PositiveHalfLineProjection

theorem doubledShiftRadialProjection_comp_intersectionProjection
    (b : ℝ) :
    doubledShiftRadialProjection b ∘L
        doubledShiftSoninIntersectionProjection b =
      doubledShiftSoninIntersectionProjection b := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply]
  apply (Submodule.starProjection_eq_self_iff).mpr
  exact ((doubledShiftSoninClosedSubspace b).toSubmodule.starProjection_apply_mem u).1

theorem intersectionProjection_comp_doubledShiftRadialProjection
    (b : ℝ) :
    doubledShiftSoninIntersectionProjection b ∘L
        doubledShiftRadialProjection b =
      doubledShiftSoninIntersectionProjection b := by
  have h := congrArg ContinuousLinearMap.adjoint
    (doubledShiftRadialProjection_comp_intersectionProjection b)
  simpa only [ContinuousLinearMap.adjoint_comp,
    (doubledShiftRadialProjection_isStarProjection b).isSelfAdjoint.adjoint_eq,
    (doubledShiftSoninIntersectionProjection_isStarProjection b).isSelfAdjoint.adjoint_eq]
    using h

theorem sourceFourierSupportProjection_comp_intersectionProjection
    (b : ℝ) :
    sourceFourierSupportProjection unitSoninScale ∘L
        doubledShiftSoninIntersectionProjection b =
      doubledShiftSoninIntersectionProjection b := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply]
  change (ccm24ArchimedeanFourierSupportClosedSubspace unitSoninScale).toSubmodule.starProjection
      (doubledShiftSoninIntersectionProjection b u) = _
  apply (Submodule.starProjection_eq_self_iff).mpr
  exact ((doubledShiftSoninClosedSubspace b).toSubmodule.starProjection_apply_mem u).2

theorem intersectionProjection_comp_sourceFourierSupportProjection
    (b : ℝ) :
    doubledShiftSoninIntersectionProjection b ∘L
        sourceFourierSupportProjection unitSoninScale =
      doubledShiftSoninIntersectionProjection b := by
  have h := congrArg ContinuousLinearMap.adjoint
    (sourceFourierSupportProjection_comp_intersectionProjection b)
  simpa only [ContinuousLinearMap.adjoint_comp,
    (sourceFourierSupportProjection_isStarProjection unitSoninScale).isSelfAdjoint.adjoint_eq,
    (doubledShiftSoninIntersectionProjection_isStarProjection b).isSelfAdjoint.adjoint_eq]
    using h

theorem doubledShiftProlateDefectFactor_eq_rawSupportCrossing
    (b : ℝ) :
    doubledShiftProlateDefectFactor b =
      doubledShiftRawSupportCrossing b := by
  let P : Op := doubledShiftRadialProjection b
  let Q : Op := sourceFourierSupportProjection unitSoninScale
  let R : Op := doubledShiftSoninIntersectionProjection b
  have hP : P * P = P := by
    dsimp [P]
    exact (doubledShiftRadialProjection_isStarProjection b).isIdempotentElem
  have hR : R * R = R := by
    dsimp [R]
    exact (doubledShiftSoninIntersectionProjection_isStarProjection b).isIdempotentElem
  have hPR : P * R = R := by
    dsimp [P, R]
    exact doubledShiftRadialProjection_comp_intersectionProjection b
  have hRP : R * P = R := by
    dsimp [P, R]
    exact intersectionProjection_comp_doubledShiftRadialProjection b
  have hQR : Q * R = R := by
    dsimp [Q, R]
    exact sourceFourierSupportProjection_comp_intersectionProjection b
  have hRQ : R * Q = R := by
    dsimp [Q, R]
    exact intersectionProjection_comp_sourceFourierSupportProjection b
  have hcancel :
      (1 - P + R) * R = R := by
    calc
      (1 - P + R) * R = R - P * R + R * R := by noncomm_ring
      _ = R := by rw [hPR, hR]; abel
  have hcross :
      (1 - P + R) * Q * P = (1 - P) * Q * P + R := by
    calc
      (1 - P + R) * Q * P = (1 - P) * Q * P + R * Q * P := by
        noncomm_ring
      _ = (1 - P) * Q * P + R := by rw [hRQ, hRP]
  have hright : (1 - P + R) * Q * R = R := by
    calc
      (1 - P + R) * Q * R = (1 - P + R) * (Q * R) := by
        noncomm_ring
      _ = (1 - P + R) * R := by rw [hQR]
      _ = R := hcancel
  change
    (1 - (P - R)) * (Q * (P - R)) =
      (1 - P) * Q * P
  calc
    (1 - (P - R)) * (Q * (P - R)) =
        (1 - P + R) * Q * P - (1 - P + R) * Q * R := by
          noncomm_ring
    _ = (1 - P + R) * Q * P - R := by
          rw [hright]
    _ = (1 - P) * Q * P := by rw [hcross]; abel

theorem doubledShiftRadialProjection_conjugate
    (b : ℝ) :
    (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap ∘L
        doubledShiftRadialProjection b ∘L
          (cc20GlobalLogTranslation (-2 * b)).toContinuousLinearMap =
      cc20PositiveHalfLineProjection := by
  let T : Op := (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap
  let Tm : Op := (cc20GlobalLogTranslation (-2 * b)).toContinuousLinearMap
  let P : Op := cc20PositiveHalfLineProjection
  have hT : T * Tm = (1 : Op) := by
    dsimp [T, Tm]
    have hzero :
        (cc20GlobalLogTranslation 0).toContinuousLinearMap = (1 : Op) := by
      simpa only [ContinuousLinearMap.one_def] using unitTranslation_zero_operator
    calc
      (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap *
          (cc20GlobalLogTranslation (-2 * b)).toContinuousLinearMap =
          (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap *
            (cc20GlobalLogTranslation (-(2 * b))).toContinuousLinearMap := by
              congr 2 <;> ring
      _ = (cc20GlobalLogTranslation 0).toContinuousLinearMap := by
            simpa only [ContinuousLinearMap.mul_def,
              show 2 * b + -(2 * b) = 0 by ring] using
              (rawGlobalLogTranslation_comp (2 * b) (-(2 * b)))
      _ = 1 := hzero
  have hP : doubledShiftRadialProjection b = Tm * P * T := by
    convert (doubledShiftRadialProjection_eq_translatedHalfLineProjection b) using 1 <;>
      simp only [T, Tm, P, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_assoc] <;> ring
  rw [hP]
  calc
    T * (Tm * P * T) * Tm = (T * Tm) * P * (T * Tm) := by
      noncomm_ring
    _ = P := by rw [hT]; simp

theorem sourceFourierSupportProjection_unit_eq_hardy_conjugation :
    sourceFourierSupportProjection unitSoninScale =
      (ccm24ArchimedeanHardyTitchmarsh : Op) ∘L
        cc20PositiveHalfLineProjection ∘L
          (ccm24ArchimedeanHardyTitchmarsh : Op) := by
  rw [sourceFourierSupportProjection_unit]
  simpa only [archimedeanHardyTitchmarshOperator] using
    unitTransportedHalfLineProjection_eq_hardyConjugation

theorem doubledShiftRawSupportCrossing_conjugate_eq_shiftedHardyCrossing
    (b : ℝ) :
    (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap ∘L
        doubledShiftRawSupportCrossing b ∘L
      (cc20GlobalLogTranslation (-2 * b)).toContinuousLinearMap =
      doubledShiftHardyRawSupportCrossing b := by
  let T : Op := (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap
  let Tm : Op := (cc20GlobalLogTranslation (-(2 * b))).toContinuousLinearMap
  let P : Op := cc20PositiveHalfLineProjection
  let H : Op := ccm24ArchimedeanHardyTitchmarsh
  let K : Op := doubledShiftHardy b
  let Q : Op := sourceFourierSupportProjection unitSoninScale
  let R : Op := doubledShiftRadialProjection b
  have hTmT : ∀ x : Carrier, Tm (T x) = x := by
    intro x
    dsimp [T, Tm]
    have hzero :
        (cc20GlobalLogTranslation 0).toContinuousLinearMap =
          ContinuousLinearMap.id ℂ Carrier :=
      unitTranslation_zero_operator
    have hcomp := rawGlobalLogTranslation_comp (-(2 * b)) (2 * b)
    have hcomp' :
        (cc20GlobalLogTranslation (-(2 * b))).toContinuousLinearMap ∘L
            (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap =
          ContinuousLinearMap.id ℂ Carrier := by
      calc
        (cc20GlobalLogTranslation (-(2 * b))).toContinuousLinearMap ∘L
            (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap =
            (cc20GlobalLogTranslation (-(2 * b) + 2 * b)).toContinuousLinearMap := by
              simpa only [ContinuousLinearMap.mul_def] using hcomp
        _ = (cc20GlobalLogTranslation 0).toContinuousLinearMap := by
              congr 2 <;> ring
        _ = ContinuousLinearMap.id ℂ Carrier := hzero
    have hx := congrArg (fun L : Op => L x) hcomp'
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hx
  have hp : ∀ x : Carrier, T (R (Tm x)) = P x := by
    intro x
    have h := doubledShiftRadialProjection_conjugate b
    have hx := congrArg (fun L : Op => L x) h
    simpa only [T, Tm, P, R, ContinuousLinearMap.comp_apply,
      show -2 * b = -(2 * b) by ring] using hx
  have hHTm : ∀ x : Carrier, H (Tm x) = T (H x) := by
    intro x
    have h := archimedeanHardyTitchmarsh_comp_globalLogTranslation (-(2 * b))
    have hx := congrArg (fun L : Op => L x) h
    simpa only [T, Tm, H, ContinuousLinearMap.comp_apply,
      show -(-(2 * b)) = 2 * b by ring] using hx
  have hq : ∀ x : Carrier, T (Q (Tm x)) = K (P (K x)) := by
    intro x
    have hQ : Q = H ∘L P ∘L H := by
      dsimp [Q, H, P]
      simpa only [ContinuousLinearMap.comp_assoc] using
        sourceFourierSupportProjection_unit_eq_hardy_conjugation
    rw [hQ]
    change T (H (P (H (Tm x)))) = K (P (K x))
    rw [hHTm x]
    rfl
  have hcomp : ∀ x : Carrier, T ((ContinuousLinearMap.id ℂ Carrier - R) (Tm x)) =
      (ContinuousLinearMap.id ℂ Carrier - P) x := by
    intro x
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub]
    have hTTm : ∀ y : Carrier, T (Tm y) = y := by
      intro y
      dsimp [T, Tm]
      have hzero :
          (cc20GlobalLogTranslation 0).toContinuousLinearMap =
            ContinuousLinearMap.id ℂ Carrier :=
        unitTranslation_zero_operator
      have hcomp := rawGlobalLogTranslation_comp (2 * b) (-(2 * b))
      have hcomp' :
          (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap ∘L
              (cc20GlobalLogTranslation (-(2 * b))).toContinuousLinearMap =
            ContinuousLinearMap.id ℂ Carrier := by
        calc
          (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap ∘L
              (cc20GlobalLogTranslation (-(2 * b))).toContinuousLinearMap =
              (cc20GlobalLogTranslation (2 * b + -(2 * b))).toContinuousLinearMap := by
                simpa only [ContinuousLinearMap.mul_def] using hcomp
          _ = (cc20GlobalLogTranslation 0).toContinuousLinearMap := by
                congr 2 <;> ring
          _ = ContinuousLinearMap.id ℂ Carrier := hzero
      have hy := congrArg (fun L : Op => L y) hcomp'
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using hy
    rw [hTTm x, hp x]
  apply ContinuousLinearMap.ext
  intro u
  have hR : ∀ x : Carrier, R (Tm x) = Tm (P x) := by
    intro x
    have h := hp x
    have hx := congrArg (fun y : Carrier => Tm y) h
    change Tm (T (R (Tm x))) = Tm (P x) at hx
    rw [hTmT (R (Tm x))] at hx
    exact hx
  have hinside :
      T (Q (Tm (P u))) = K (P (K (P u))) := hq (P u)
  have houter : ∀ y : Carrier,
      T ((ContinuousLinearMap.id ℂ Carrier - R) y) =
        (ContinuousLinearMap.id ℂ Carrier - P) (T y) := by
    intro y
    have hy := hcomp (T y)
    rw [hTmT y] at hy
    exact hy
  have hgoal :
      T ((ContinuousLinearMap.id ℂ Carrier - R) (Q (R (Tm u)))) =
        (ContinuousLinearMap.id ℂ Carrier - P) (K (P (K (P u)))) := by
    rw [hR u, houter, hinside]
  simpa only [T, Tm, P, H, K, Q, R,
    doubledShiftRawSupportCrossing, doubledShiftHardyRawSupportCrossing,
    ContinuousLinearMap.comp_apply,
    show -2 * b = -(2 * b) by ring] using hgoal

private lemma neg_window_identity {R : Type*} [Ring R]
    (M P K : R) (hK : K * K = 1) (hMP : M * P = 0)
    (hPM : P + M = 1) :
    M * K * P * K * P = -(M * K * M * K * P) := by
  apply (eq_neg_iff_add_eq_zero).2
  calc
    M * K * P * K * P + M * K * M * K * P =
        M * K * (P + M) * K * P := by
          noncomm_ring
    _ = M * K * 1 * K * P := by rw [hPM]
    _ = M * (K * K) * P := by noncomm_ring
    _ = M * P := by rw [hK]; simp
    _ = 0 := hMP

theorem doubledShiftRawSupportCrossing_eq_negative_shiftedHardyWindow
    (b : ℝ) :
    doubledShiftHardyRawSupportCrossing b =
      -(ContinuousLinearMap.id ℂ Carrier - cc20PositiveHalfLineProjection) ∘L
        doubledShiftHardy b ∘L
          (ContinuousLinearMap.id ℂ Carrier - cc20PositiveHalfLineProjection) ∘L
            doubledShiftHardy b ∘L cc20PositiveHalfLineProjection := by
  let P : Op := cc20PositiveHalfLineProjection
  let M : Op := ContinuousLinearMap.id ℂ Carrier - P
  let K : Op := doubledShiftHardy b
  have hK : K * K = (1 : Op) := by
    dsimp [K]
    simpa only [ContinuousLinearMap.mul_def] using doubledShiftHardy_involutive b
  have hMP : M * P = 0 := by
    dsimp [M]
    have hP : P * P = P := by
      exact cc20PositiveHalfLineProjection_isIdempotentElem
    calc
      (1 - P) * P = P - P * P := by noncomm_ring
      _ = 0 := by rw [hP, sub_self]
  have hPM : P + M = (1 : Op) := by
    dsimp [M]
    noncomm_ring
  unfold doubledShiftHardyRawSupportCrossing
  change M * K * P * K * P = -(M * K * M * K * P)
  exact neg_window_identity M P K hK hMP hPM

end Dev
end ConnesWeilRH
