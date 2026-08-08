import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Complex.Basic

/-!
# Critical-line Gamma center rigidity

Groundwork for the archimedean sign `Re[Gamma(a + I/2)^4] >= 0` on a band.

Pins the center facts that are provable in mathlib v4.30 without a Stirling
asymptotic:

* `Complex.Gamma (1/2)` is a real number: `im = 0` and `0 < re`.
* `Complex.Gamma (1/2) != 0`.
* points on the critical line `Re z = 1/2` are never poles of Gamma.

This gives the honest statement that the phase `arg(Gamma(1/2 + I t))` is `0`
at `t = 0` (and continuous there by the pole-free lemma).  It does NOT by
itself certify `Re (Gamma(a + I/2)^4) >= 0` on a positive-width band: mathlib
v4.30 has no `Gamma(1/2) = sqrt pi`, no complex-Gamma Stirling/argument bound,
and `Complex.Gamma` is non-computable, so a genuine phase window needs a real
mathlib extension (see `docs/proofs/869_gamma_stirling_gap.md`).

Target axioms: [propext, Classical.choice, Quot.sound].
-/
namespace ConnesWeilRH
namespace Source
namespace Dev
namespace GammaCenterRealSolidity

open Complex

/-- The imaginary part of `Gamma (1/2 : Complex)` is zero. -/
theorem gamma_center_one_half_im_zero : (Gamma ((1 / 2 : ℝ) : ℂ)).im = 0 := by
  rw [Complex.Gamma_ofReal (1 / 2 : ℝ)]
  simp

/-- The real part of `Gamma (1/2 : Complex)` is strictly positive. -/
theorem gamma_center_one_half_re_pos : 0 < (Gamma ((1 / 2 : ℝ) : ℂ)).re := by
  rw [Complex.Gamma_ofReal (1 / 2 : ℝ)]
  exact Real.Gamma_pos_of_pos (by norm_num : 0 < (1 / 2 : ℝ))

/-- `Complex.Gamma (1/2)` does not vanish (no pole at `Re z = 1/2`). -/
theorem gamma_center_one_half_ne_zero : Complex.Gamma ((1 / 2 : ℝ) : ℂ) ≠ 0 := by
  exact Complex.Gamma_ne_zero_of_re_pos (by norm_num : 0 < ((1 / 2 : ℝ) : ℂ).re)

/-- Points on the critical line `Re z = 1/2` are never poles of Gamma, i.e.
never a non-positive integer. -/
lemma critical_line_no_pole (t : ℝ) : ∀ m : ℕ, (1 / 2 : ℂ) + Complex.I * (t : ℂ) ≠ -(m : ℂ) := by
  intro m hm
  have hz : (((1 / 2 : ℂ) + Complex.I * (t : ℂ)).re) = (1 / 2 : ℝ) := by simp
  have hn : ((-(m : ℂ)) : ℂ).re = -(m : ℝ) := by simp
  have hmid : (((1 / 2 : ℂ) + Complex.I * (t : ℂ)).re) = ((-(m : ℂ)) : ℂ).re := by
    exact (congrArg Complex.re hm.symm).symm
  have hre_eq : (1 / 2 : ℝ) = -(m : ℝ) := hz.symm.trans (hmid.trans hn)
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith

end GammaCenterRealSolidity
end Dev
end Source
end ConnesWeilRH