/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3KernelReadback
import ConnesWeilRH.Dev.C1G8R3KernelRowRepresentative

/-!
# Canonical Lp readback on the Schwartz core

The earlier Schwartz readback is written with the Schwartz function itself,
while the Plancherel operator consumes its `toLp` class.  This leaf combines
that readback with representative independence, yielding the exact formula
with the canonical `MemLp.toLp` representative.  It is the dense-core
statement needed before a continuity/density extension; it makes no claim for
arbitrary L2 inputs.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source.CCM25Concrete.CompactLogConvolution

theorem sourceKernelReadback_ae_toLp_core
    (g : CompactLogTest) (u : SchwartzMap ℝ ℂ) :
    (Source.CC20Concrete.cc20GlobalLogConvolution g.involution.test
        (u.toLp 2) : ℝ → ℂ) =ᵐ[volume]
      (fun t : ℝ => ∫ x : ℝ,
        ((SchwartzMap.memLp u (ENNReal.ofReal 2)).toLp u : ℝ → ℂ) x *
          star (g.test (x - t))) := by
  have hread := sourceKernelReadback_ae g u
  filter_upwards [hread] with t ht
  rw [ht]
  exact sourceKernelRow_integral_eq_toLp_rep g
    (SchwartzMap.memLp u (ENNReal.ofReal 2)) t

end Dev
end ConnesWeilRH
