/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1DigammaVerticalLine

/-!
# C3' Gamma_R logarithmic-derivative bound

The carrier shift is already exact.  This leaf supplies the magnitude bound
needed when its shifted Xi weight is paired with the Gamma_R kernel.  It uses
the committed digamma vertical-half-plane estimate and the exact
Gamma_R/digamma formula; it does not assert a sign for the real part.
-/

namespace ConnesWeilRH
namespace Dev

open Complex

theorem norm_logDeriv_GammaR_le_of_re_ge_half
    {s : Complex} (hs : (1 : Real) / 2 ≤ s.re) :
    ‖logDeriv Complex.Gammaℝ s‖ ≤
      ‖(Complex.log (Real.pi : Complex)) / 2‖ +
        (1 / 2 : Real) *
          ((‖Complex.digamma ((1 / 2 : Real) : Complex)‖ + 4 + 6 / 5) +
            (12 / 5 : Real) * ‖s / 2‖) := by
  have hspos : 0 < s.re := by linarith
  have hRe : (s / 2).re = s.re / 2 := by
    norm_num [Complex.div_re, Complex.normSq_apply]
  have hquarter : (1 : Real) / 4 ≤ (s / 2).re := by
    rw [hRe]
    linarith
  have hdigamma := abs_digamma_le_of_re_ge_quarter hquarter
  have hdigamma' :
      ‖Complex.digamma (s / 2)‖ ≤
        (‖Complex.digamma ((1 / 2 : Real) : Complex)‖ + 4 + 6 / 5) +
          (12 / 5 : Real) * ‖s / 2‖ := by
    simpa using hdigamma
  rw [Source.C1XiCenterTwoGamma.logDeriv_GammaR_eq_log_pi_add_digamma hspos]
  calc
    ‖-(Complex.log (Real.pi : Complex)) / 2 +
          (1 / 2 : Complex) * Complex.digamma (s / 2)‖ ≤
        ‖-(Complex.log (Real.pi : Complex)) / 2‖ +
          ‖(1 / 2 : Complex) * Complex.digamma (s / 2)‖ :=
      norm_add_le _ _
    _ = ‖(Complex.log (Real.pi : Complex)) / 2‖ +
          (1 / 2 : Real) * ‖Complex.digamma (s / 2)‖ := by
      rw [neg_div, norm_neg, norm_mul]
      norm_num
    _ ≤ ‖(Complex.log (Real.pi : Complex)) / 2‖ +
          (1 / 2 : Real) *
            ((‖Complex.digamma ((1 / 2 : Real) : Complex)‖ + 4 + 6 / 5) +
              (12 / 5 : Real) * ‖s / 2‖) := by
      gcongr

end Dev
end ConnesWeilRH
