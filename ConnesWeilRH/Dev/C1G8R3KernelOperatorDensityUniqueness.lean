/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3KernelReadbackLpCore

/-!
# Dense-core uniqueness for the root convolution operator

The remaining row-readback theorem should construct a continuous operator on
the L2 carrier.  This leaf isolates the uniqueness step: agreement with the
Plancherel root convolution on the Schwartz `toLp` core forces equality on all
of L2 by Mathlib's dense-range theorem.  No row estimate or sign is assumed.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete.CompactLogConvolution

theorem rootConvolution_eq_of_schwartz_core
    (g : CompactLogTest)
    (T : cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2)
    (hT : ∀ u : SchwartzMap ℝ ℂ,
      T (u.toLp 2) = cc20GlobalLogConvolution g.involution.test (u.toLp 2)) :
    T = cc20GlobalLogConvolution g.involution.test := by
  apply ContinuousLinearMap.ext
  intro u
  apply DenseRange.induction_on (p := fun v =>
      T v = cc20GlobalLogConvolution g.involution.test v)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) u
  · apply isClosed_eq
    · exact T.continuous
    · exact (cc20GlobalLogConvolution g.involution.test).continuous
  · intro v
    exact hT v

end Dev
end ConnesWeilRH
