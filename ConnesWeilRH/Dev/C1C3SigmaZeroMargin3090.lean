import ConnesWeilRH.Dev.C1C3SigmaKernel

/-!
# Route A c3Sigma zero margin reduction (record 3090)

The exact remaining special-function obligation is a strict upper bound on the
real part of `digamma (1/4)`. This module records the reduction without hiding
that bound behind a numerical constant.
-/

namespace ConnesWeilRH
namespace Dev
namespace C1C3SigmaZeroMargin3090

theorem c3Sigma_zero_pos_of_digamma_re_lt_log_pi
    (hdig : (Complex.digamma ((1 / 4 : Real) : Complex)).re < Real.log Real.pi) :
    0 < c3Sigma 0 := by
  simpa [c3Sigma] using (sub_pos.mpr hdig)

theorem digamma_zero_margin_target :
    0 < c3Sigma 0 ↔
      (Complex.digamma ((1 / 4 : Real) : Complex)).re < Real.log Real.pi := by
  simp [c3Sigma]

end C1C3SigmaZeroMargin3090
end Dev
end ConnesWeilRH
