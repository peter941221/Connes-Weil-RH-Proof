/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3KernelReadbackL2Limit
import ConnesWeilRH.Dev.C1CC20KernelLpLift
import ConnesWeilRH.Dev.C1Stage3FrontierHS

/-!
# L2 convergence of inputs gives pointwise kernel-row convergence

The row Holder estimate is written with an ordinary real integral, while the
approximating input sequence is naturally controlled in `Lp`.  This leaf
closes precisely that norm-interface gap using the existing L2 square-root
readback and `MemLp.toLp_sub`.  It proves no global output estimate and no
positivity statement.
-/

namespace ConnesWeilRH
namespace Dev

open Filter MeasureTheory
open Source.C1CC20KernelLpLift
open Source.C1Stage3FrontierHS
open Source.CCM25Concrete.CompactLogConvolution
open scoped Topology

theorem sourceKernelRow_integral_tendsto_of_schwartz_l2_tendsto
    (g : CompactLogTest) {u : ℝ → ℂ}
    (hu : MemLp u 2 (volume : Measure ℝ))
    (u_seq : ℕ → SchwartzMap ℝ ℂ)
    (hLp : Tendsto
      (fun n => (u_seq n).toLp 2) atTop (𝓝 (hu.toLp u))) (t : ℝ) :
    Tendsto
      (fun n => ∫ x : ℝ, u_seq n x * star (g.test (x - t))) atTop
      (𝓝 (∫ x : ℝ, u x * star (g.test (x - t)))) := by
  have hu' : MemLp u (ENNReal.ofReal 2) := by
    simpa using hu
  have hmem' : ∀ n, MemLp (u_seq n) (ENNReal.ofReal 2) := by
    intro n
    exact SchwartzMap.memLp (u_seq n) (ENNReal.ofReal 2)
  have hmem₂ : ∀ n, MemLp (u_seq n) 2 := by
    intro n
    simpa using hmem' n
  have hLp' : Tendsto
      (fun n => (hmem₂ n).toLp (u_seq n)) atTop
        (𝓝 (hu.toLp u)) := by
    simpa only using hLp
  have hnorm : Tendsto
      (fun n => ‖(hmem₂ n).toLp (u_seq n) - hu.toLp u‖) atTop
        (𝓝 0) := by
    have hdist := (tendsto_iff_dist_tendsto_zero.mp hLp')
    simpa only [dist_eq_norm] using hdist
  have hroot : Tendsto
      (fun n =>
        (∫ x : ℝ, ‖u_seq n x - u x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) atTop
        (𝓝 0) := by
    apply hnorm.congr'
    exact Eventually.of_forall fun n => by
      have hdiff : MemLp ((u_seq n : ℝ → ℂ) - u) 2
          (volume : Measure ℝ) := (hmem₂ n).sub hu
      calc
        ‖(hmem₂ n).toLp (u_seq n) - hu.toLp u‖ =
            ‖hdiff.toLp ((u_seq n : ℝ → ℂ) - u)‖ := by
          rw [MemLp.toLp_sub]
        _ = lpNorm ((u_seq n : ℝ → ℂ) - u) 2 volume := by
          exact frontierLp2normToReal hdiff
        _ = (∫ x : ℝ, ‖u_seq n x - u x‖ ^ (2 : ℝ)) ^
            (1 / (2 : ℝ)) := by
          simpa only [Pi.sub_apply] using
            (frontierLp2normEqIntegralSqrt hdiff)
  have hbound : Tendsto
      (fun n =>
        (∫ x : ℝ, ‖u_seq n x - u x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫ x : ℝ, ‖star (g.test (x - t))‖ ^ (2 : ℝ)) ^
            (1 / (2 : ℝ))) atTop (𝓝 0) := by
    simpa only [zero_mul] using hroot.mul tendsto_const_nhds
  exact sourceKernelRow_integral_tendsto_of_holder_bound
    g hu' hmem' t hbound

end Dev
end ConnesWeilRH
