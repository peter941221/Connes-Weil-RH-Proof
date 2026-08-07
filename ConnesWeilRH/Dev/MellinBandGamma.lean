import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
Band-test Mellin to Complex.Gamma (859 follow-up).

On the faithful log carrier, doc 859 narrowed the sign slot to
`Re[(M g (i/2))^4] >= 0`.  For the band test `f_a(t) = t^a * e^(-t)` (a > 0,
multiplicative coordinate) the closed Mellin is

    mellin (fun t => e^(-t) * t^a) (i/2) = Complex.Gamma (a + i/2)

via (1) the Mellin shift `mellin_cpow_smul` and (2) the identification of
`mellin (fun t => e^(-t)) z` with `Complex.Gamma z` (Euler's integral, 0 < re z).
Payoff: a NONZERO, well-defined band test whose critical-line Mellin is a
genuine Gamma value, so the sign slot is non-trivial (not the vacuous 0-producer
AGENTS §6/§11 forbids).  We do NOT claim the sign Re[(Gamma(a+i/2))^4] >= 0
(that open phase bound is 859); only that the object exists and is nonzero.

Target axioms: [propext, Classical.choice, Quot.sound].
-/
namespace ConnesWeilRH
namespace Source
namespace Dev
namespace MellinBandGamma

noncomputable section
open MeasureTheory Set
open scoped Topology

/-- `mellin (e^(-t)) z` agrees pointwise with Euler's `Complex.GammaIntegral z`. -/
lemma mellin_expNeg_eq_GammaIntegral (z : ℂ) :
    mellin (fun t : ℝ => (Real.exp (-t) : ℂ)) z = Complex.GammaIntegral z := by
  rw [Complex.GammaIntegral, mellin]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  -- (t : ℂ)^(z-1) • e^(-t) = e^(-t) * (t : ℂ)^(z-1)
  simp only [smul_eq_mul, mul_comm]

/-- Euler's integral identification: `mellin (fun t => e^(-t)) z = Gamma z`
   whenever `0 < re z`. -/
theorem mellin_expNeg_eq_Gamma (z : ℂ) (hz : 0 < z.re) :
    mellin (fun t : ℝ => (Real.exp (-t) : ℂ)) z = Complex.Gamma z := by
  rw [Complex.Gamma_eq_integral hz]
  exact mellin_expNeg_eq_GammaIntegral z

/-- Band integrand sits as `t^a • e^(-t)`, so the Mellin shift applies:
   `s ↦ s + a`. -/
lemma mellin_band_shift (a : ℂ) (s : ℂ) :
    mellin (fun t : ℝ => (Real.exp (-t) : ℂ) * (t : ℂ) ^ a) s =
      mellin (fun t : ℝ => (Real.exp (-t) : ℂ)) (s + a) := by
  simpa [smul_eq_mul, mul_comm] using
    (mellin_cpow_smul (fun t : ℝ => (Real.exp (-t) : ℂ)) s a)

/-- The faithful band-test closed Mellin:
   `mellin (t ↦ e^(-t) t^a) (i/2) = Gamma (a + i/2)` for `a > 0`. -/
theorem mellin_band_eq_Gamma (a : ℝ) (ha : 0 < a) :
    mellin (fun t : ℝ => (Real.exp (-t) : ℂ) * (t : ℂ) ^ (a : ℂ)) (Complex.I / 2) =
      Complex.Gamma ((a : ℂ) + Complex.I / 2) := by
  rw [mellin_band_shift ((a : ℂ)) (Complex.I / 2)]
  have hz : 0 < (Complex.I / 2 + (a : ℂ)).re := by
    rw [Complex.add_re, Complex.div_re]
    norm_num
    simpa using ha
  rw [mellin_expNeg_eq_Gamma (Complex.I / 2 + (a : ℂ)) hz]
  congr 1
  rw [add_comm]

/-- The band test's critical-line Mellin is NONZERO for every `a > 0`.  This is
   the well-defined, non-vacuous evaluation the sign slot needs (859): it rules
   out the empty 0-producer (AGENTS §6/§11). -/
theorem mellin_band_ne_zero (a : ℝ) (ha : 0 < a) :
    mellin (fun t : ℝ => (Real.exp (-t) : ℂ) * (t : ℂ) ^ (a : ℂ)) (Complex.I / 2) ≠ 0 := by
  rw [mellin_band_eq_Gamma a ha]
  exact Complex.Gamma_ne_zero_of_re_pos (by
    rw [Complex.add_re, Complex.div_re]
    norm_num
    simpa using ha)

end
end MellinBandGamma
end Dev
end Source
end ConnesWeilRH


