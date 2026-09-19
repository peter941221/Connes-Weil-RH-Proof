/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3AnnularPointwiseReadback
import ConnesWeilRH.Dev.C1CC20KernelLpLift

/-!
# L2 energy readback of the source-root annulus

The pointwise annulus identity is now converted into the exact squared L2
energy identity consumed by the S3 diagonal estimate.  This is a readback
theorem only: it supplies no uniform bound or sign.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source.CC20Concrete
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.SelectedCrossingOperatorBridge
open Source.CCM25Concrete.SelectedWeilSquare

theorem sourceRootAnnularOutputWindow_normSq_eq_annulus_integral
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (N n : ℕ) (hNn : N ≤ n) (u : sourceSoninCarrier lambda) :
    ‖sourceRootAnnularOutputWindow owner lambda N n u‖ ^ 2 =
      ∫ t, ‖(Set.Icc (-(n : ℝ)) (n : ℝ) \
        Set.Icc (-(N : ℝ)) (N : ℝ)).indicator
          (fun s => (rootConvolution owner (sourceInclusion lambda u) :
            ℝ → ℂ) s) t‖ ^ 2 := by
  let v := sourceRootAnnularOutputWindow owner lambda N n u
  have hv : MemLp (v : ℝ → ℂ) 2 volume := Lp.memLp v
  have hnorm :=
    Source.C1CC20KernelLpLift.norm_toLp_sq_eq_integral_norm_sq hv
  have hto : hv.toLp (v : ℝ → ℂ) = v := Lp.toLp_coeFn v hv
  have hread :=
    sourceRootAnnularOutputWindow_coeFn_eq_annulus_indicator
      owner lambda N n hNn u
  calc
    ‖v‖ ^ 2 = ‖hv.toLp (v : ℝ → ℂ)‖ ^ 2 := by rw [hto]
    _ = ∫ t, ‖(v : ℝ → ℂ) t‖ ^ 2 := hnorm
    _ = ∫ t, ‖(Set.Icc (-(n : ℝ)) (n : ℝ) \
        Set.Icc (-(N : ℝ)) (N : ℝ)).indicator
          (fun s => (rootConvolution owner (sourceInclusion lambda u) :
            ℝ → ℂ) s) t‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hread] with t ht
      rw [ht]

end Dev
end ConnesWeilRH
