/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3AnnularL2EnergyReadback

/-!
# Tonelli bridge for the source-root annular kernel diagonal

The nonnegative squared column energies can be exchanged with the spatial
integral without assuming the desired finite bound.  This isolates the
remaining S3 producer as a pointwise kernel-diagonal estimate after Tonelli.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source.CC20Concrete
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.SelectedWeilSquare

theorem sourceRootAnnularOutputWindow_lintegral_tsum_eq_tsum_lintegral
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (N n : ℕ) {ι : Type*} [Countable ι]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)) :
    ∫⁻ t, (∑' i : ι,
      ‖(sourceRootAnnularOutputWindow owner lambda N n
        (sourceBasis i) : ℝ → ℂ) t‖ₑ ^ (2 : ℝ)) =
      ∑' i : ι, ∫⁻ t,
        ‖(sourceRootAnnularOutputWindow owner lambda N n
          (sourceBasis i) : ℝ → ℂ) t‖ₑ ^ (2 : ℝ) := by
  rw [lintegral_tsum]
  intro i
  exact (Lp.aestronglyMeasurable
    (sourceRootAnnularOutputWindow owner lambda N n (sourceBasis i))).enorm
    |>.pow_const _

end Dev
end ConnesWeilRH
