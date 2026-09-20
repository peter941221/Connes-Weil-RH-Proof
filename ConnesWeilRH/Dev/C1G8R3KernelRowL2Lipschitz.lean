/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3KernelRowRepresentative

/-!
# Pointwise L2 Lipschitz estimate for a kernel row

For a fixed output point, the honest root row is pairing against a translated
reflected Schwartz kernel.  Hölder's inequality therefore controls the
difference of two row integrals by the L2 norm of the input difference and the
L2 norm of that kernel.  This is the continuity estimate needed in the density
extension; it makes no claim about the global output L2 norm or positivity.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source.C1CC20TranslateInvariance
open Source.CCM25Concrete.CompactLogConvolution

theorem sourceKernelRow_integral_norm_sub_le
    (g : CompactLogTest) {u v : ℝ → ℂ}
    (hu : MemLp u (ENNReal.ofReal 2))
    (hv : MemLp v (ENNReal.ofReal 2)) (t : ℝ) :
    ‖(∫ x : ℝ, u x * star (g.test (x - t))) -
        (∫ x : ℝ, v x * star (g.test (x - t)))‖ ≤
      (∫ x : ℝ, ‖(u x - v x)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
        (∫ x : ℝ, ‖star (g.test (x - t))‖ ^ (2 : ℝ)) ^
          (1 / (2 : ℝ)) := by
  have hkernel : MemLp (fun x : ℝ => star (g.test (x - t)))
      (ENNReal.ofReal 2) := by
    have hg : MemLp (g.involution.test : ℝ → ℂ) (ENNReal.ofReal 2) := by
      simpa using (SchwartzMap.memLp g.involution.test (ENNReal.ofReal 2))
    have hshift := memLp_shift hg t
    have hneg := hshift.comp_measurePreserving (Measure.measurePreserving_neg volume)
    convert hneg using 1
    funext x
    simp only [Function.comp_def, CompactLogTest.involution_apply]
    congr 2
    ring
  have hdiff : MemLp (fun x : ℝ => u x - v x) (ENNReal.ofReal 2) :=
    hu.sub hv
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hprod := integral_mul_norm_le_Lp_mul_Lq hholder hdiff hkernel
  have hu_int := sourceKernelRow_integrable_of_memLp g hu t
  have hv_int := sourceKernelRow_integrable_of_memLp g hv t
  calc
    ‖(∫ x : ℝ, u x * star (g.test (x - t))) -
          (∫ x : ℝ, v x * star (g.test (x - t)))‖ =
        ‖∫ x : ℝ, (u x - v x) * star (g.test (x - t))‖ := by
      rw [← integral_sub hu_int hv_int]
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ ≤ ∫ x : ℝ, ‖(u x - v x) * star (g.test (x - t))‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x : ℝ, ‖u x - v x‖ * ‖star (g.test (x - t))‖ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [norm_mul]
    _ ≤ (∫ x : ℝ, ‖(u x - v x)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫ x : ℝ, ‖star (g.test (x - t))‖ ^ (2 : ℝ)) ^
            (1 / (2 : ℝ)) := hprod

end Dev
end ConnesWeilRH
