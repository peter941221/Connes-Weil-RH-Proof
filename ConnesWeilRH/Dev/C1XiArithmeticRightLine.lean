import ConnesWeilRH.Dev.C1XiVerticalFunctional
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# C1XiArithmeticRightLine - the pointwise arithmetic right-line brick

On `Re s > 1`, this module factors the same completed xi owner into the
elementary pole factors, the real Gamma factor, and the ordinary Riemann zeta
function.  Mathlib's von Mangoldt L-series theorem then reads the zeta factor
back as the complete prime-power arithmetic term.

This is deliberately pointwise.  It does not yet identify the interval
integral of the right-line kernel with `C1SameOwnerWeil.psi`; the archimedean
integral and the exchange of the L-series with that integral remain separate
owners.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiArithmeticRightLine

open CC20ZetaCounting
open C1XiVerticalFunctional
open Complex
open Filter
open scoped LSeries.notation Topology

noncomputable section

/-- Mathlib's von Mangoldt L-series, named for the arithmetic right-line API. -/
noncomputable def vonMangoldtLSeries (s : Complex) : Complex :=
  L ↗ArithmeticFunction.vonMangoldt s

/-- The completed zeta factor is Gamma_R times the ordinary zeta function to
the right of the line `Re s = 1`. -/
theorem completedRiemannZeta_eq_GammaR_mul_riemannZeta_of_one_lt_re
    {s : Complex} (hs : 1 < s.re) :
    completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  have hgamma : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  rw [riemannZeta_def_of_ne_zero hs0]
  field_simp [hgamma]

theorem completedRiemannZeta_ne_zero_of_one_lt_re
    {s : Complex} (hs : 1 < s.re) :
    completedRiemannZeta s ≠ 0 := by
  rw [completedRiemannZeta_eq_GammaR_mul_riemannZeta_of_one_lt_re hs]
  exact mul_ne_zero
    (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith))
    (riemannZeta_ne_zero_of_one_lt_re hs)

private theorem differentiableAt_GammaR_of_one_lt_re
    {s : Complex} (hs : 1 < s.re) :
    DifferentiableAt Complex Complex.Gammaℝ s := by
  have hgamma : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hinv : DifferentiableAt Complex
      (fun z : Complex => (Complex.Gammaℝ z)⁻¹) s :=
    Complex.differentiable_Gammaℝ_inv.differentiableAt
  have h := hinv.inv (inv_ne_zero hgamma)
  change DifferentiableAt Complex
    (fun z : Complex => ((Complex.Gammaℝ z)⁻¹)⁻¹) s at h
  simpa only [inv_inv] using h

theorem logDeriv_completedRiemannZeta_eq_GammaR_add_riemannZeta
    {s : Complex} (hs : 1 < s.re) :
    logDeriv completedRiemannZeta s =
      logDeriv Complex.Gammaℝ s + logDeriv riemannZeta s := by
  have hgamma : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hzeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  have hneighborhood : completedRiemannZeta =ᶠ[𝓝 s]
      (fun z => Complex.Gammaℝ z * riemannZeta z) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    exact completedRiemannZeta_eq_GammaR_mul_riemannZeta_of_one_lt_re hz
  calc
    logDeriv completedRiemannZeta s =
        logDeriv (fun z => Complex.Gammaℝ z * riemannZeta z) s := by
      simp only [logDeriv_apply]
      rw [hneighborhood.deriv_eq]
      congr 1
      exact hneighborhood.eq_of_nhds
    _ = logDeriv Complex.Gammaℝ s + logDeriv riemannZeta s :=
      logDeriv_mul s hgamma hzeta
        (differentiableAt_GammaR_of_one_lt_re hs)
        (differentiableAt_riemannZeta hs1)

private theorem logDeriv_shifted_id (s : Complex) :
    logDeriv (fun z : Complex => z - 1) s = 1 / (s - 1) := by
  rw [logDeriv_apply, deriv_sub_const]
  simp

theorem logDeriv_completedRiemannXi_eq_pole_GammaR_zeta
    {s : Complex} (hs : 1 < s.re) :
    logDeriv completedRiemannXi s =
      1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s +
        logDeriv riemannZeta s := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  have hshift : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hgamma : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hzeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hxiZeta : completedRiemannZeta s ≠ 0 :=
    completedRiemannZeta_ne_zero_of_one_lt_re hs
  have hneighborhood : completedRiemannXi =ᶠ[𝓝 s]
      (fun z => z * (z - 1) * completedRiemannZeta z) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    exact completedRiemannXi_eq_mul_completedRiemannZeta
      (Complex.ne_zero_of_one_lt_re hz) (by
        intro h
        subst z
        norm_num at hz)
  have hlinear : logDeriv (fun z : Complex => z * (z - 1)) s =
      1 / s + 1 / (s - 1) := by
    calc
      logDeriv (fun z : Complex => z * (z - 1)) s =
          logDeriv (fun z : Complex => z) s +
            logDeriv (fun z : Complex => z - 1) s :=
        logDeriv_mul s hs0 hshift differentiableAt_id
          (differentiableAt_id.sub_const 1)
      _ = 1 / s + 1 / (s - 1) := by
        rw [show logDeriv (fun z : Complex => z) s = 1 / s by
          simp,
          logDeriv_shifted_id s]
  calc
    logDeriv completedRiemannXi s =
        logDeriv (fun z => z * (z - 1) * completedRiemannZeta z) s := by
      simp only [logDeriv_apply]
      rw [hneighborhood.deriv_eq]
      congr 1
      exact hneighborhood.eq_of_nhds
    _ = logDeriv (fun z : Complex => z * (z - 1)) s +
          logDeriv completedRiemannZeta s := by
      exact logDeriv_mul s (mul_ne_zero hs0 hshift) hxiZeta
        ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)))
        (differentiableAt_completedZeta hs0 hs1)
    _ = 1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s +
          logDeriv riemannZeta s := by
      rw [hlinear, logDeriv_completedRiemannZeta_eq_GammaR_add_riemannZeta hs]
      ring

theorem vonMangoldtLSeries_eq_neg_riemannZeta_logDeriv
    {s : Complex} (hs : 1 < s.re) :
    vonMangoldtLSeries s = -logDeriv riemannZeta s := by
  unfold vonMangoldtLSeries
  simpa only [logDeriv_apply, neg_div] using
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs)

/-- Pointwise arithmetic readback of the negative xi logarithmic derivative.
The final L-series is the complete von Mangoldt prime-power series; no
finite-support truncation or interval-integral exchange is hidden here. -/
theorem negativeXiLogDeriv_eq_vonMangoldtLSeries_add_GammaR
    {s : Complex} (hs : 1 < s.re) :
    negativeXiLogDeriv s =
      -(1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s) +
        vonMangoldtLSeries s := by
  have hzeta := vonMangoldtLSeries_eq_neg_riemannZeta_logDeriv hs
  calc
    negativeXiLogDeriv s =
        -(1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s +
          logDeriv riemannZeta s) := by
      rw [negativeXiLogDeriv,
        logDeriv_completedRiemannXi_eq_pole_GammaR_zeta hs]
    _ = -(1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s) -
          logDeriv riemannZeta s := by ring
    _ = -(1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s) +
          vonMangoldtLSeries s := by
      rw [sub_eq_add_neg]
      rw [show -logDeriv riemannZeta s = vonMangoldtLSeries s by exact hzeta.symm]

end
end C1XiArithmeticRightLine
end Source
end ConnesWeilRH
