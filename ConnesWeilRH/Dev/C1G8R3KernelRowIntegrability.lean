/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20UniformSlice
import ConnesWeilRH.Source.CC20Concrete.CompactRootHalfLinePair

/-!
# Integrability of one root-convolution kernel row

For an arbitrary `L2` input `u`, this leaf proves that the honest row
integral against the reflected compact-log test is genuinely integrable at
each output displacement.  The proof reflects the input, uses the existing
translation-invariant `MemLp` infrastructure, and then transports
integrability back through negation.  It does not identify the row integral
with the Plancherel convolution on the full `Lp` space.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source.C1CC20UniformSlice
open Source.C1CC20TranslateInvariance
open Source.CCM25Concrete.CompactLogConvolution

theorem sourceKernelRow_integrable_of_memLp
    (g : CompactLogTest) {u : ℝ → ℂ}
    (hu : MemLp u (ENNReal.ofReal 2)) (t : ℝ) :
    Integrable (fun x : ℝ => u x * star (g.test (x - t))) volume := by
  have hu_reflect : MemLp (fun x : ℝ => u (-x)) (ENNReal.ofReal 2) := by
    simpa only [Function.comp_def] using
      hu.comp_measurePreserving (Measure.measurePreserving_neg volume)
  have hg : MemLp (g.involution.test : ℝ → ℂ) (ENNReal.ofReal 2) := by
    simpa using (SchwartzMap.memLp g.involution.test (ENNReal.ofReal 2))
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  letI : ENNReal.HolderConjugate (ENNReal.ofReal 2) (ENNReal.ofReal 2) :=
    hholder.ennrealOfReal
  have hslice : Integrable
      (fun x : ℝ => u (-x) * g.involution.test (x + t)) volume := by
    simpa only [Pi.mul_apply] using
      hu_reflect.integrable_mul (memLp_shift hg t)
  have htransport :=
    (Measure.measurePreserving_neg volume).integrable_comp_of_integrable hslice
  convert htransport using 1
  funext x
  simp only [Function.comp_apply, neg_neg, sub_eq_add_neg,
    CompactLogTest.involution_apply]
  ring

end Dev
end ConnesWeilRH
