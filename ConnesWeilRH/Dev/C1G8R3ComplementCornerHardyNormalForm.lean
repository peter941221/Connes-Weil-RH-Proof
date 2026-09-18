/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ShiftedHardyKernelReduction

/-!
# S3 complement corner in shifted-Hardy coordinates

The exact leakage corner is transported to the positive-half-line block
`P - P K_b P K_b P`.  This is a normal form only: it does not assert a
Hilbert--Schmidt estimate for the corner.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier
local notation "Op" => Carrier →L[ℂ] Carrier

theorem doubledShiftComplementCorner_conjugate_eq_hardyDefect (b : ℝ) :
    doubledShiftCarrierTranslation b ∘L
        (doubledShiftRadialProjection b ∘L
          (ContinuousLinearMap.id ℂ Carrier -
            sourceFourierSupportProjection unitSoninScale) ∘L
          doubledShiftRadialProjection b) ∘L
        doubledShiftCarrierTranslationInv b =
      cc20PositiveHalfLineProjection -
        (cc20PositiveHalfLineProjection ∘L doubledShiftHardy b ∘L
          cc20PositiveHalfLineProjection ∘L doubledShiftHardy b ∘L
          cc20PositiveHalfLineProjection) := by
  let T : Op := doubledShiftCarrierTranslation b
  let Tm : Op := doubledShiftCarrierTranslationInv b
  let P : Op := cc20PositiveHalfLineProjection
  let K : Op := doubledShiftHardy b
  let R : Op := doubledShiftRadialProjection b
  let Q : Op := sourceFourierSupportProjection unitSoninScale
  have hTTm : T ∘L Tm = ContinuousLinearMap.id ℂ Carrier := by
    simpa only [T, Tm] using doubledShiftCarrierTranslation_comp_inv b
  have hTmT : Tm ∘L T = ContinuousLinearMap.id ℂ Carrier := by
    simpa only [T, Tm] using doubledShiftCarrierTranslationInv_comp b
  have hR : T ∘L R ∘L Tm = P := by
    simpa only [T, Tm, R, P] using
      doubledShiftCarrierTranslation_conjugate_radial b
  have hQ : T ∘L Q ∘L Tm = K ∘L P ∘L K := by
    have hQ0 := doubledShiftCarrierTranslation_conjugate_fourier b
    apply ContinuousLinearMap.ext
    intro u
    have hu := congrArg (fun L : Op => L u) hQ0
    simpa only [T, Tm, Q, K, P, ContinuousLinearMap.comp_apply,
      cc20TransportedHalfLineProjection_apply,
      doubledShiftHardyTranslationEquiv_symm_apply] using hu
  have hmiddle : T ∘L (ContinuousLinearMap.id ℂ Carrier - Q) ∘L Tm =
      ContinuousLinearMap.id ℂ Carrier - K ∘L P ∘L K := by
    simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id,
      ContinuousLinearMap.sub_comp, ContinuousLinearMap.id_comp, hQ]
    rw [hTTm]
  have hP : P ∘L P = P := by
    dsimp [P]
    exact cc20PositiveHalfLineProjection_isIdempotentElem
  calc
    T ∘L R ∘L (ContinuousLinearMap.id ℂ Carrier - Q) ∘L R ∘L Tm =
        (T ∘L R ∘L Tm) ∘L
          (T ∘L (ContinuousLinearMap.id ℂ Carrier - Q) ∘L Tm) ∘L
            (T ∘L R ∘L Tm) := by
              calc
                T ∘L R ∘L (ContinuousLinearMap.id ℂ Carrier - Q) ∘L R ∘L Tm =
                    T ∘L R ∘L (Tm ∘L T) ∘L
                      (ContinuousLinearMap.id ℂ Carrier - Q) ∘L
                      (Tm ∘L T) ∘L R ∘L Tm := by
                        rw [hTmT]
                        simp only [ContinuousLinearMap.id_comp,
                          ContinuousLinearMap.comp_id]
                _ = (T ∘L R ∘L Tm) ∘L
                    (T ∘L (ContinuousLinearMap.id ℂ Carrier - Q) ∘L Tm) ∘L
                      (T ∘L R ∘L Tm) := by
                        simp only [ContinuousLinearMap.comp_assoc]
    _ = P - P ∘L K ∘L P ∘L K ∘L P := by
      rw [hR, hmiddle]
      simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id,
        ContinuousLinearMap.sub_comp, ContinuousLinearMap.id_comp,
        ContinuousLinearMap.comp_assoc]
      rw [hP]

end Dev
end ConnesWeilRH
