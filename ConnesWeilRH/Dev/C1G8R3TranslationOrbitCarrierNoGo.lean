/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3HardyTranslatedTail
import ConnesWeilRH.Dev.C1G8R3SoninCarrierStructureBricks

/-!
# No full right-translation orbit inside the source Sonin carrier

The Hardy tail theorem gives norm decay of the source Fourier-support
projection along the right-translated orbit.  On the Sonin carrier that
projection is the identity, while logarithmic translation is an isometry.
Therefore a nonzero carrier vector cannot have its entire right-translated
orbit inside the carrier.  This closes the overly strong translation-based
noncompactness shortcut; it does not estimate the S3 kernel diagonal.
-/

namespace ConnesWeilRH
namespace Dev

open Filter
open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSSoninCarrierStructure
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment
open Source.CC20Concrete.CCM24SoninCarrierInvariance
open scoped Topology

theorem sourceSonin_nonzero_not_closed_under_all_right_translations
    (u : finiteSCarrier)
    (hu : u ∈ (ccm24ArchimedeanSoninClosedSubspace unitSoninScale).toSubmodule)
    (horbit : ∀ n : ℕ,
      cc20GlobalLogTranslation (-(n : ℝ)) u ∈
        (ccm24ArchimedeanSoninClosedSubspace unitSoninScale).toSubmodule) :
    u = 0 := by
  have hproj (n : ℕ) :
      sourceFourierSupportProjection unitSoninScale
          (cc20GlobalLogTranslation (-(n : ℝ)) u) =
        cc20GlobalLogTranslation (-(n : ℝ)) u := by
    exact sourceFourierSupportProjection_eq_self_of_mem_sonin
      unitSoninScale (horbit n)
  have hdecay :=
    sourceFourierSupportProjection_unit_globalLogTranslation_neg_tendsto_zero u
  have hnormdecay :
      Tendsto
        (fun n : ℕ => ‖sourceFourierSupportProjection unitSoninScale
          (cc20GlobalLogTranslation (-(n : ℝ)) u)‖)
        atTop (𝓝 0) := by
    simpa only [Function.comp_apply, norm_zero] using
      (continuous_norm.tendsto 0).comp hdecay
  have hconstant : ∀ n : ℕ,
      ‖sourceFourierSupportProjection unitSoninScale
          (cc20GlobalLogTranslation (-(n : ℝ)) u)‖ = ‖u‖ := by
    intro n
    rw [hproj n, norm_cc20GlobalLogTranslation]
  have hnormu : Tendsto (fun _ : ℕ => ‖u‖) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, hconstant] using hnormdecay
  have hnormeq : ‖u‖ = 0 := by
    exact (tendsto_nhds_unique hnormu tendsto_const_nhds).symm
  exact norm_eq_zero.mp hnormeq

end Dev
end ConnesWeilRH
