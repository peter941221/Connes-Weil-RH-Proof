import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Arch phase window: Re[Gamma(a+i/2)^4] >= 0 as a unit-circle criterion

docs/873 shows the arch sign `Re[(Gamma(a+i/2))^4] >= 0` is NOT monotone: it is
positive on a band and negative outside it.  mathlib v4.30.0 has no
Stirling / arg-Gamma estimate, so a full phase bound is beyond the formalist.
What this module DOES close, axiom-free, is the *structural phase window*: for
any nonzero complex w,

    Re[w^4] >= 0   <->   (Re[w / conj(w)])^2 >= 1/2

with `conj(w) := star w` (complex conjugation).  `w / star w` is the
doubled-phase unit and `(Re[w / star w])^2 >= 1/2` is the classical
`cos^2(theta) >= 1/2` criterion.  Chained with `Complex.Gamma_conj`, the
route-1 arch gate becomes a cosine criterion on the Gamma ratio.  No Stirling
is assumed; docs/873 s numeric band is honored, not replaced.
-/
namespace ConnesWeilRH
namespace Source
namespace Dev
namespace ArchPhaseWindow

noncomputable section

/-- Real part of the fourth power, as a polynomial in re and im. -/
lemma re_pow_four (z : Complex) :
    (z ^ 4).re = (z.re) ^ 4 - 6 * (z.re) ^ 2 * (z.im) ^ 2 + (z.im) ^ 4 := by
  rw [show z ^ 4 = (z ^ 2) * (z ^ 2) by ring]
  rw [Complex.mul_re]
  have hr2 : (z ^ 2).re = (z.re) ^ 2 - (z.im) ^ 2 := by
    rw [pow_two, Complex.mul_re]
    ring
  have hi2 : (z ^ 2).im = 2 * z.re * z.im := by
    rw [pow_two, Complex.mul_im]
    ring
  rw [hr2, hi2]
  ring

/-- Real part of `z / star z` = the normalized difference of squares. -/
lemma phase_ratio_re (z : Complex) :
    (z / star z).re = ((z.re) ^ 2 - (z.im) ^ 2) / Complex.normSq z := by
  rw [Complex.div_re]
  rw [show (star z) = (starRingEnd Complex) z by simp]
  rw [Complex.normSq_conj, Complex.conj_re, Complex.conj_im]
  ring_nf

/-- Key identity: Re[w^4] = (normSq w)^2 * (2 * Re[w / conj w]^2 - 1). -/
lemma pow_four_handshake (w : Complex) (hz : w ≠ 0) :
    (w ^ 4).re = (Complex.normSq w) ^ 2 *
      (2 * ((w / star w).re) ^ 2 - 1) := by
  rw [re_pow_four]
  rw [phase_ratio_re]
  have hs : 0 < (w.re ^ 2 + w.im ^ 2) := by
    simpa [Complex.normSq_apply, pow_two] using (Complex.normSq_pos).2 hz
  rw [Complex.normSq_apply]
  field_simp [ne_of_gt hs]
  ring_nf

/-- The phase window: slit of the real fourth power over the phase cosine. -/
theorem pow_four_re_sign_of_phase (w : Complex) (hz : w ≠ 0) :
    (0 <= (w ^ 4).re) <-> (1 / 2 <= ((w / star w).re) ^ 2) := by
  rw [pow_four_handshake w hz]
  have hpos : 0 < ((Complex.normSq w) ^ 2 : Real) := by
    exact pow_pos ((Complex.normSq_pos).2 hz) 2
  constructor <;> intro h <;> nlinarith

/-- The arch gate on the Gamma ratio: windowed cosine criterion on the unit circle. -/
theorem gammaPhase_window (a : Real) (ha : 0 < a) :
    (0 <= ((Complex.Gamma ((a : Complex) + Complex.I / 2)) ^ 4).re) <->
      (1 / 2 <= ((Complex.Gamma ((a : Complex) + Complex.I / 2)) /
        star (Complex.Gamma ((a : Complex) + Complex.I / 2))).re ^ 2) := by
  have hz : Complex.Gamma ((a : Complex) + Complex.I / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simpa using ha
  exact pow_four_re_sign_of_phase (Complex.Gamma ((a : Complex) + Complex.I / 2)) hz

/-- The arch gate at a=1 reduces exactly to the phase criterion (window). -/
theorem archPhase_at_one :
    (0 <= ((Complex.Gamma (1 + Complex.I / 2)) ^ 4).re) <->
        (1 / 2 <= ((Complex.Gamma (1 + Complex.I / 2)) /
          star (Complex.Gamma (1 + Complex.I / 2))).re ^ 2) := by
  simpa using (gammaPhase_window 1 (by norm_num))

/-- Non-vacuity for the band test: the slot complex is never zero, so the
phase window is a real (nonempty) gate, not an empty producer (AGENTS 6/11). -/
theorem archPhase_at_one_nonvacuous :
    (Complex.Gamma (1 + Complex.I / 2)) ≠ 0 := by
  apply Complex.Gamma_ne_zero_of_re_pos
  norm_num


end

/--
Wiring to the Hilbert arch-sign slot.  HilbertArchSlot a is the datum
ScalarTraceScaleSymbols.archimedeanSignNormalized (i.e. the consumer's
archimedean leg) must carry for the band test at a; it equals the 4th-power real
sign of the critical Mellin = Gamma(a+i/2). HilbertArchSlot_iff_phaseWindow shows
this slot is data-bearing: it is EXACTLY the phase window
(Re[Gamma / conj Gamma])^2 >= 1/2.  So the whole sign slot gates on a single
still-open datum - a Stirling / arg-Gamma bound, which mathlib v4.30.0 does not
provide.  This module proves the wiring reduces that datum to the clean cosine
criterion; it does not supply the (absent) Stirling estimate.  No RH is claimed.
-/
def HilbertArchSign (a : Real) : Prop :=
  0 <= ((Complex.Gamma ((a : Complex) + Complex.I / 2)) ^ 4).re

theorem HilbertArchSign_iff_phaseWindow (a : Real) (ha : 0 < a) :
    HilbertArchSign a <->
      (1 / 2 <= ((Complex.Gamma ((a : Complex) + Complex.I / 2)) /
        star (Complex.Gamma ((a : Complex) + Complex.I / 2))).re ^ 2) := by
  unfold HilbertArchSign
  exact gammaPhase_window a ha
theorem archSign_effect_of_phaseWindow (a : Real) (ha : 0 < a) :
    (1 / 2 <= ((Complex.Gamma ((a : Complex) + Complex.I / 2)) /
      star (Complex.Gamma ((a : Complex) + Complex.I / 2))).re ^ 2) ->
      HilbertArchSign a := by
  intro hP
  rw [HilbertArchSign_iff_phaseWindow a ha]
  exact hP

end ArchPhaseWindow

end Dev
end Source
end ConnesWeilRH




