/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3SchwartzApproximation

/-!
# Arbitrary-L2 kernel readback

The dense-range approximation and the complete Schwartz-limit readback now
compose into the final representative-level kernel formula for every L2
input.  This is the readback endpoint consumed by the annular S3 analysis.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source.CCM25Concrete.CompactLogConvolution
open Source.CC20Concrete
open scoped Topology

theorem sourceKernelReadback_ae_arbitrary_l2
    (g : CompactLogTest) {u : ℝ → ℂ}
    (hu : MemLp u 2 (volume : Measure ℝ)) :
    (cc20GlobalLogConvolution g.involution.test
      (hu.toLp u) : ℝ → ℂ) =ᵐ[volume]
      (fun t : ℝ => ∫ x : ℝ, u x * star (g.test (x - t))) := by
  obtain ⟨u_seq, hLp⟩ := exists_schwartz_l2_tendsto (u := hu.toLp u)
  exact sourceKernelReadback_ae_of_schwartz_l2_tendsto g hu u_seq hLp

end Dev
end ConnesWeilRH
