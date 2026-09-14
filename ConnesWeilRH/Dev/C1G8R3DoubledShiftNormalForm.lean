/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ZeroDefectClosure

/-!
# R3 doubled-shift Hardy involution

The scale defect has an exact relative-motion normal form.  Its new object is
the translated Hardy transform `K_b = T_(2b) H`.  This leaf proves the first
structural fact about that object: it is an involution for every real b.
No trace estimate, detector sign, or RH premise is used.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.C1SemilocalHardyTitchmarshUnitarityReduction

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier
local notation "Op" => Carrier →L[ℂ] Carrier

noncomputable def doubledShiftHardy (b : ℝ) : Op :=
  (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap ∘L
    (ccm24ArchimedeanHardyTitchmarsh : Carrier →L[ℂ] Carrier)

theorem doubledShiftHardy_apply (b : ℝ) (u : Carrier) :
    doubledShiftHardy b u =
      (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap
        (ccm24ArchimedeanHardyTitchmarsh u) := by
  rfl

theorem rawGlobalLogTranslation_comp (a c : ℝ) :
    (cc20GlobalLogTranslation a).toContinuousLinearMap ∘L
        (cc20GlobalLogTranslation c).toContinuousLinearMap =
      (cc20GlobalLogTranslation (a + c)).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro u
  exact cc20GlobalLogTranslation_add_apply a c u

theorem doubledShiftHardy_involutive (b : ℝ) :
    doubledShiftHardy b ∘L doubledShiftHardy b =
      ContinuousLinearMap.id ℂ Carrier := by
  unfold doubledShiftHardy
  apply ContinuousLinearMap.ext
  intro u
  have hHsq :
      ccm24ArchimedeanHardyTitchmarsh
          (ccm24ArchimedeanHardyTitchmarsh u) = u :=
    ccm24ArchimedeanHardyTitchmarsh_involutive u
  have hcov :
      ccm24ArchimedeanHardyTitchmarsh
          (cc20GlobalLogTranslation (2 * b)
            (ccm24ArchimedeanHardyTitchmarsh u)) =
        cc20GlobalLogTranslation (-(2 * b))
          (ccm24ArchimedeanHardyTitchmarsh
            (ccm24ArchimedeanHardyTitchmarsh u)) := by
    exact archimedeanHardyTitchmarsh_globalLogTranslation (2 * b)
      (ccm24ArchimedeanHardyTitchmarsh u)
  have hcov' :
      (ccm24ArchimedeanHardyTitchmarsh : Carrier →L[ℂ] Carrier)
          ((cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap
            (ccm24ArchimedeanHardyTitchmarsh u)) =
        (cc20GlobalLogTranslation (-(2 * b))).toContinuousLinearMap
          ((ccm24ArchimedeanHardyTitchmarsh : Carrier →L[ℂ] Carrier)
            ((ccm24ArchimedeanHardyTitchmarsh : Carrier →L[ℂ] Carrier) u)) := by
    simpa only [ContinuousLinearMap.coe_coe] using hcov
  change (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap
      ((ccm24ArchimedeanHardyTitchmarsh : Carrier →L[ℂ] Carrier)
        ((cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap
          ((ccm24ArchimedeanHardyTitchmarsh : Carrier →L[ℂ] Carrier) u))) = u
  have hstep :
      (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap
          ((ccm24ArchimedeanHardyTitchmarsh : Carrier →L[ℂ] Carrier)
            ((cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap
              ((ccm24ArchimedeanHardyTitchmarsh : Carrier →L[ℂ] Carrier) u))) =
        (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap
          ((cc20GlobalLogTranslation (-(2 * b))).toContinuousLinearMap
            ((ccm24ArchimedeanHardyTitchmarsh : Carrier →L[ℂ] Carrier)
              ((ccm24ArchimedeanHardyTitchmarsh : Carrier →L[ℂ] Carrier) u))) := by
    exact congrArg (fun v : Carrier =>
      (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap v) hcov'
  have hHsq' :
      (ccm24ArchimedeanHardyTitchmarsh : Carrier →L[ℂ] Carrier)
          ((ccm24ArchimedeanHardyTitchmarsh : Carrier →L[ℂ] Carrier) u) = u := by
    simpa only [ContinuousLinearMap.coe_coe] using hHsq
  rw [hstep, hHsq']
  have htrans :
      (cc20GlobalLogTranslation (2 * b)).toContinuousLinearMap
          ((cc20GlobalLogTranslation (-(2 * b))).toContinuousLinearMap u) =
        (cc20GlobalLogTranslation ((2 * b) + -(2 * b))).toContinuousLinearMap u := by
    simpa only [ContinuousLinearMap.coe_coe] using
      cc20GlobalLogTranslation_add_apply (2 * b) (-(2 * b)) u
  rw [htrans]
  rw [show (2 * b) + -(2 * b) = 0 by ring]
  have hzero (v : Carrier) : cc20GlobalLogTranslation 0 v = v := by
    apply (cc20GlobalLogTranslation 0).injective
    simpa only [zero_add] using cc20GlobalLogTranslation_add_apply 0 0 v
  simpa only [ContinuousLinearMap.coe_coe] using hzero u

end Dev
end ConnesWeilRH
