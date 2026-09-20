/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3KernelRowL2Lipschitz

/-!
# Pointwise convergence of kernel rows under an L2 bound

This is the sequential form of the preceding Lipschitz estimate.  It is
deliberately stated with the explicit Holder majorant as a hypothesis: the
remaining global L2 step must still supply that majorant from the chosen
Schwartz approximation and then identify the output representative.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Filter
open Source.CCM25Concrete.CompactLogConvolution
open scoped Topology

theorem sourceKernelRow_integral_tendsto_of_holder_bound
    (g : CompactLogTest) {u : ℝ → ℂ} {u_seq : ℕ → ℝ → ℂ}
    (hu : MemLp u (ENNReal.ofReal 2))
    (hu_seq : ∀ n, MemLp (u_seq n) (ENNReal.ofReal 2)) (t : ℝ)
    (hbound : Tendsto
      (fun n =>
        (∫ x : ℝ, ‖u_seq n x - u x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫ x : ℝ, ‖star (g.test (x - t))‖ ^ (2 : ℝ)) ^
            (1 / (2 : ℝ))) atTop (𝓝 0)) :
    Tendsto
      (fun n => ∫ x : ℝ, u_seq n x * star (g.test (x - t))) atTop
      (𝓝 (∫ x : ℝ, u x * star (g.test (x - t)))) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg)
  · intro n
    simpa only [dist_eq_norm] using
      sourceKernelRow_integral_norm_sub_le g (hu_seq n) hu t
  · exact hbound

end Dev
end ConnesWeilRH
