import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule

/-  2457 (obligation W-A of record 2455): the one-sided panel
quadrature bound.  Mathlib's trapezoidal_error_le_of_c2 bounds the
ABSOLUTE error of uniform trapezoidal integration on a panel by
|b-a|^3 * zeta / (12 * N^2) whenever the integrand is C^2 with second
derivative bounded by zeta.  The strip consumer needs the one-sided
UPPER direction (integral <= trapezoid + error).  Owner-independent,
no numerical data.  -/

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-- One-sided panel bound: the integral of a `C^2` function whose
second derivative is bounded by `ζ` is at most its uniform trapezoidal
sum plus the Mathlib error term.  This is the Lean half of the 2342
point-sum + panel decomposition; the node values and the `ζ` bound are
hypotheses here and become the attachment obligation (W-C). -/
theorem panelQuadrature_le_2457 {g : ℝ → ℝ} {a b ζ : ℝ} {N : ℕ}
    (hN : 0 < N) (hab : a ≤ b)
    (h_c2 : ContDiffOn ℝ 2 g (Set.uIcc a b))
    (hζ : ∀ x, |iteratedDerivWithin 2 g (Set.uIcc a b) x| ≤ ζ) :
    ∫ x in a..b, g x ≤
      trapezoidal_integral g N a b + (b - a) ^ 3 * ζ / (12 * N ^ 2) := by
  have habs := trapezoidal_error_le_of_c2 h_c2 hζ hN
  unfold trapezoidal_error at habs
  rw [abs_of_nonneg (show 0 ≤ b - a from by linarith)] at habs
  have hpair := abs_le.mp habs
  linarith [hpair.1, hpair.2]

/-- The strip-shaped instance: weighted modulus of a complex function,
the integrand shape of `stripNorm`.  The `ζ` hypothesis is exactly the
2342 panel factor `exp(|sigma| R) (m_(k+2) + 2|sigma| m_(k+1) +
sigma^2 m_k)` once the attachment (W-C) supplies the `m_j` sup bounds
for the actual owner family. -/
theorem stripPanelQuadrature_expNorm_le_2457 {F : ℝ → ℂ} {a b σ ζ : ℝ}
    {N : ℕ} (hN : 0 < N) (hab : a ≤ b)
    (h_c2 : ContDiffOn ℝ 2 (fun x => Real.exp (σ * x) * ‖F x‖) (Set.uIcc a b))
    (hζ : ∀ x,
      |iteratedDerivWithin 2 (fun x => Real.exp (σ * x) * ‖F x‖)
        (Set.uIcc a b) x| ≤ ζ) :
    ∫ x in a..b, Real.exp (σ * x) * ‖F x‖ ≤
      trapezoidal_integral (fun x => Real.exp (σ * x) * ‖F x‖) N a b
        + (b - a) ^ 3 * ζ / (12 * N ^ 2) :=
  panelQuadrature_le_2457 hN hab h_c2 hζ

end ConnesWeilRH.Dev
