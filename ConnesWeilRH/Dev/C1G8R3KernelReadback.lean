/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.CompactRootHalfLinePair
import ConnesWeilRH.Source.CC20Concrete.GlobalLogConvolution

/-!
# Kernel readback of the root convolution (record 1734, the section-3 face)

Record 1734 section 3 prices the annular kernel diagonal by the honest
kernel-pairing integral: on Schwartz inputs the Plancherel-defined root
convolution agrees (a.e., on the `L2` representative) with

`(C u)(t) = ∫ x, u x * conj (test (x - t)) dx`,

i.e. the pairing against the reflected kernel `k_t = conj (test (t - ·))`;
at `t = 0` this is the committed `k_0 = conj (test (-·))`.

This leaf lands that face from three committed inputs:

1. the Schwartz-face bridge `cc20GlobalLogConvolution_toLp`
   (the Plancherel-defined operator agrees with the Schwartz convolution
   `toLp`-for-`toLp`),
2. Mathlib's representative lemma `SchwartzMap.coeFn_toLp`,
3. the pointwise kernel-integral identity
   `fullBoundaryIntegral_eq_globalConvolutionCore`
   (the honest pairing integral equals the Schwartz convolution value).

No carrier object, no annular bound, and no sign is touched here.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source.CC20Concrete.CompactRootHalfLinePair

/-- **Kernel readback** (record 1734 section 3).  On Schwartz inputs the
root convolution's `L2` representative is, almost everywhere, the honest
kernel-pairing integral against the reflected test. -/
theorem sourceKernelReadback_ae
    (g : Source.CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (u : SchwartzMap ℝ ℂ) :
    (Source.CC20Concrete.cc20GlobalLogConvolution g.involution.test (u.toLp 2) :
      ℝ → ℂ)
      =ᵐ[volume]
        (fun t : ℝ => ∫ x : ℝ, u x * star (g.test (x - t))) := by
  have h1 :
      (Source.CC20Concrete.cc20GlobalLogConvolution g.involution.test
          (u.toLp 2) : ℝ → ℂ)
        =ᵐ[volume]
          (SchwartzMap.convolution (ContinuousLinearMap.mul ℝ ℂ)
            g.involution.test u : ℝ → ℂ) := by
    rw [Source.CC20Concrete.cc20GlobalLogConvolution_toLp g.involution.test u]
    exact SchwartzMap.coeFn_toLp _ 2 (volume : Measure ℝ)
  filter_upwards [h1] with t ht
  rw [ht]
  exact (fullBoundaryIntegral_eq_globalConvolutionCore g u t).symm

end Dev
end ConnesWeilRH
