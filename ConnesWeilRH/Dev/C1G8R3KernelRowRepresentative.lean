/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3KernelRowIntegrability

/-!
# Representative independence of a root-kernel row

The Plancherel operator is an `Lp` object, while the honest kernel row is
written using a function representative.  This leaf records the exact
representative bridge: for every `MemLp` input, replacing the input by its
canonical `toLp` representative does not change the row integral.  Together
with the row-integrability theorem, this is the representative-safe socket
needed by a later density/readback argument.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source.CCM25Concrete.CompactLogConvolution

theorem sourceKernelRow_integral_eq_toLp_rep
    (g : CompactLogTest) {u : ℝ → ℂ}
    (hu : MemLp u (ENNReal.ofReal 2)) (t : ℝ) :
    (∫ x : ℝ, u x * star (g.test (x - t))) =
      (∫ x : ℝ, (hu.toLp u : ℝ → ℂ) x * star (g.test (x - t))) := by
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp] with x hx
  rw [hx]

end Dev
end ConnesWeilRH
