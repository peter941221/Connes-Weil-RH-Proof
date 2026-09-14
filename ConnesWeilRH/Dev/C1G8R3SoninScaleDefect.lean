/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScaleProlateAlignment

/-!
# The exact Hardy--translation defect for the G8 source prolate owner

The radial projection is a translated half-line projection.  If the concrete
Hardy--Titchmarsh transform anti-commuted with the same translation, the
source Fourier projection would be a unitary translate of its unit-scale
version.  This file isolates the exact defect of that covariance identity.

This is deliberately an identity, not an estimate: it does not assume the
missing Fourier-translation theorem and it does not turn a conditional
covariance into a fact.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier
local notation "Op" => Carrier →L[ℂ] Carrier

noncomputable def hardyOperator : Op :=
  ccm24ArchimedeanHardyTitchmarsh.toContinuousLinearEquiv.toContinuousLinearMap

noncomputable def logTranslation (b : ℝ) : Op :=
  (cc20GlobalLogTranslation b).toContinuousLinearMap

noncomputable def hardyTranslationRightDefect (b : ℝ) : Op :=
  logTranslation b ∘L hardyOperator -
    hardyOperator ∘L logTranslation (-b)

noncomputable def hardyTranslationLeftDefect (b : ℝ) : Op :=
  hardyOperator.adjoint ∘L logTranslation (-b) -
    logTranslation b ∘L hardyOperator.adjoint

theorem conjugated_projection_sub_ideal
    (H Hstar Tplus Tminus P : Op) :
    (Hstar ∘L Tminus ∘L P ∘L Tplus ∘L H) -
        (Tplus ∘L Hstar ∘L P ∘L H ∘L Tminus) =
      (Hstar ∘L Tminus - Tplus ∘L Hstar) ∘L P ∘L Tplus ∘L H +
        Tplus ∘L Hstar ∘L P ∘L (Tplus ∘L H - H ∘L Tminus) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, map_sub]
  noncomm_ring

theorem sourceFourierSupportProjection_sub_scale_ideal
    (lambda : CCM24SoninScale) :
    sourceFourierSupportProjection lambda -
        logTranslation (Real.log lambda) ∘L
          sourceFourierSupportProjection unitSoninScale ∘L
            logTranslation (-Real.log lambda) =
      hardyTranslationLeftDefect (Real.log lambda) ∘L
          cc20PositiveHalfLineProjection ∘L
            logTranslation (Real.log lambda) ∘L hardyOperator +
        logTranslation (Real.log lambda) ∘L hardyOperator.adjoint ∘L
          cc20PositiveHalfLineProjection ∘L
            hardyTranslationRightDefect (Real.log lambda) := by
  let b : ℝ := Real.log lambda
  let H : Op := hardyOperator
  let Tplus : Op := logTranslation b
  let Tminus : Op := logTranslation (-b)
  let P : Op := cc20PositiveHalfLineProjection
  have hradial : radialSupportProjection lambda =
      Tminus ∘L P ∘L Tplus := by
    unfold radialSupportProjection Tminus Tplus P
    simpa [b] using
      (ccm24LogRadialSupportProjection_eq_translation_conjugation lambda)
  have hunit : sourceFourierSupportProjection unitSoninScale =
      H.adjoint ∘L P ∘L H := by
    rw [sourceFourierSupportProjection_unit]
    unfold H P
    rfl
  have hlambda : sourceFourierSupportProjection lambda =
      H.adjoint ∘L (radialSupportProjection lambda) ∘L H := by
    unfold sourceFourierSupportProjection H
    rw [ccm24ArchimedeanFourierSupportProjection_eq_transport]
    rfl
  rw [hlambda, hunit, hradial]
  unfold hardyTranslationLeftDefect hardyTranslationRightDefect
  exact conjugated_projection_sub_ideal H H.adjoint Tplus Tminus P

theorem sourceFourierSupportProjection_eq_scale_conjugate_of_defects_zero
    (lambda : CCM24SoninScale)
    (hleft : hardyTranslationLeftDefect (Real.log lambda) = 0)
    (hright : hardyTranslationRightDefect (Real.log lambda) = 0) :
    sourceFourierSupportProjection lambda =
      logTranslation (Real.log lambda) ∘L
        sourceFourierSupportProjection unitSoninScale ∘L
          logTranslation (-Real.log lambda) := by
  have h := sourceFourierSupportProjection_sub_scale_ideal lambda
  rw [hleft, hright] at h
  have hzero :
      sourceFourierSupportProjection lambda -
          logTranslation (Real.log lambda) ∘L
            sourceFourierSupportProjection unitSoninScale ∘L
              logTranslation (-Real.log lambda) = 0 := by
    simpa using h
  exact sub_eq_zero.mp hzero

end Dev
end ConnesWeilRH
