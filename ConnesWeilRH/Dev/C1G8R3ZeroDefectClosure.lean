/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3SoninScaleDefect
import ConnesWeilRH.Dev.C1SemilocalHardyTitchmarshUnitarityReduction

/-!
# R3-F5: zero-defect closure for the source scale transport

The R3 scale-defect normal form leaves two operator defects.  The global
Hardy--Titchmarsh translation theorem and its self-adjointness theorem are
already formal, so this leaf connects those results to the defect operators
and closes the exact scale-conjugacy branch.  It proves no trace limit and no
Weil sign.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment
open Source.C1SemilocalHardyTitchmarshUnitarityReduction

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier
local notation "Op" => Carrier →L[ℂ] Carrier

theorem hardyTranslationRightDefect_eq_zero (b : ℝ) :
    hardyTranslationRightDefect b = 0 := by
  unfold hardyTranslationRightDefect logTranslation hardyOperator
  have hcov := archimedeanHardyTitchmarsh_comp_globalLogTranslation (-b)
  simp only [neg_neg] at hcov
  rw [← hcov]
  simp

theorem hardyTranslationLeftDefect_eq_zero (b : ℝ) :
    hardyTranslationLeftDefect b = 0 := by
  unfold hardyTranslationLeftDefect logTranslation hardyOperator
  rw [archimedeanHardyTitchmarsh_adjoint_eq_self]
  have hcov := archimedeanHardyTitchmarsh_comp_globalLogTranslation (-b)
  simp only [neg_neg] at hcov
  rw [hcov]
  simp

theorem sourceFourierSupportProjection_eq_scale_conjugate_of_zero_defects
    (lambda : CCM24SoninScale) :
    sourceFourierSupportProjection lambda =
      logTranslation (Real.log lambda) ∘L
        sourceFourierSupportProjection unitSoninScale ∘L
          logTranslation (-Real.log lambda) := by
  exact sourceFourierSupportProjection_eq_scale_conjugate_of_defects_zero lambda
    (hardyTranslationLeftDefect_eq_zero (Real.log lambda))
    (hardyTranslationRightDefect_eq_zero (Real.log lambda))

end Dev
end ConnesWeilRH
