/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3KernelReadbackL2Limit
import ConnesWeilRH.Dev.C1G8R3KernelRowL2Convergence

/-!
# Complete Schwartz-L2 kernel readback

This is the consumer-facing composition of the two preceding interfaces:
Schwartz approximants have the a.e. kernel readback, and L2 convergence gives
the pointwise row limit.  Consequently the limiting Plancherel output has the
honest kernel-row formula a.e.  The annular diagonal estimate is deliberately
not included here.
-/

namespace ConnesWeilRH
namespace Dev

open Filter MeasureTheory
open Source.CC20Concrete
open Source.CCM25Concrete.CompactLogConvolution
open scoped Topology

theorem sourceKernelReadback_ae_of_schwartz_l2_tendsto
    (g : CompactLogTest) {u : ℝ → ℂ}
    (hu : MemLp u 2 (volume : Measure ℝ))
    (u_seq : ℕ → SchwartzMap ℝ ℂ)
    (hLp : Tendsto
      (fun n => (u_seq n).toLp 2) atTop (𝓝 (hu.toLp u))) :
    (cc20GlobalLogConvolution g.involution.test
      (hu.toLp u) : ℝ → ℂ) =ᵐ[volume]
      (fun t : ℝ => ∫ x : ℝ, u x * star (g.test (x - t))) := by
  exact sourceKernelReadback_ae_of_schwartz_l2_limit g hu u_seq hLp
    (fun t => sourceKernelRow_integral_tendsto_of_schwartz_l2_tendsto
      g hu u_seq hLp t)

end Dev
end ConnesWeilRH
