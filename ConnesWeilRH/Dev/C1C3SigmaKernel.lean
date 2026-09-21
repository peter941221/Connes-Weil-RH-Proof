/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1C3GammaRBound

/-!
# C3' sigma kernel

The paper's archimedean sigma profile is the real part of the same
`Gamma_R` logarithmic derivative already used by the C3 carrier.  This leaf
records that coordinate change exactly, so a later sign certificate can be
stated on the actual Gamma_R owner rather than on an unrelated special
function expression.
-/

namespace ConnesWeilRH
namespace Dev

open Complex

noncomputable def c3Sigma (xi : Real) : Real :=
  Real.log Real.pi -
    (Complex.digamma
      (((1 / 4 : Real) : Complex) - ((xi : Complex) * Complex.I) / 2)).re

theorem c3Sigma_eq_neg_two_re_logDeriv_GammaR (xi : Real) :
    c3Sigma xi =
      -2 *
        (logDeriv Complex.Gammaℝ
          (((1 / 2 : Real) : Complex) - (xi : Complex) * Complex.I)).re := by
  have hs : 0 <
      ((((1 / 2 : Real) : Complex) - (xi : Complex) * Complex.I).re) := by
    simp
  have hlog :=
    Source.C1XiCenterTwoGamma.logDeriv_GammaR_eq_log_pi_add_digamma
      (s := (((1 / 2 : Real) : Complex) - (xi : Complex) * Complex.I)) hs
  have harg :
      (((1 / 2 : Real) : Complex) - (xi : Complex) * Complex.I) / 2 =
        (((1 / 4 : Real) : Complex) - ((xi : Complex) * Complex.I) / 2) := by
    norm_num [div_eq_mul_inv]
    ring
  rw [hlog, harg]
  unfold c3Sigma
  norm_num [Complex.div_re, Complex.mul_re, Complex.log_re]
  ring_nf

end Dev
end ConnesWeilRH
