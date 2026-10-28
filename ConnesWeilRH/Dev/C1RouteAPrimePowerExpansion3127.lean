import ConnesWeilRH.Dev.C1RouteAJointSymbolData3080
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Route A prime-power expansion bridge

This module proves the algebraic identity for one owner-selected prime: its
Poisson multiplier is the real part of the full geometric prime-power series.
It does not identify that infinite series with the finite actual owner set.
The omitted finite-owner residual remains a separate obligation.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteAPrimePowerExpansion3127

open C1RouteAJointSymbolData3080
open scoped BigOperators

noncomputable section

def routeAPrimePowerRatio (p : Nat) (xi : Real) : Complex :=
  ((1 / Real.sqrt (p : Real) : Real) : Complex) *
    Complex.exp (((Real.log (p : Real) * xi : Real) : Complex) * Complex.I)

def routeAPrimePowerExpansion (p : Nat) (xi : Real) : Real :=
  2 * (∑' k : Nat, (routeAPrimePowerRatio p xi) ^ (k + 1)).re

private theorem routeAPrimePowerRatio_norm_lt_one
    (p : Nat) (hp : Nat.Prime p) (xi : Real) :
    ‖routeAPrimePowerRatio p xi‖ < 1 := by
  have hp_pos : 0 < (p : Real) := by exact_mod_cast hp.pos
  have hsqrt : 1 < Real.sqrt (p : Real) := by
    have hp_one : (1 : Real) < (p : Real) := by exact_mod_cast hp.one_lt
    have h := Real.sqrt_lt_sqrt (show (0 : Real) ≤ 1 by norm_num) hp_one
    simpa using h
  dsimp [routeAPrimePowerRatio]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr (Real.sqrt_pos.mpr hp_pos)),
    Complex.norm_exp_ofReal_mul_I]
  simp only [mul_one]
  rw [div_lt_iff₀ (Real.sqrt_pos.mpr hp_pos)]
  simpa using hsqrt

private theorem routeAPrimePowerExpansion_eq_geometric_closed_form
    (p : Nat) (hp : Nat.Prime p) (xi : Real) :
    (∑' k : Nat, (routeAPrimePowerRatio p xi) ^ (k + 1)) =
      routeAPrimePowerRatio p xi /
        (1 - routeAPrimePowerRatio p xi) := by
  let z := routeAPrimePowerRatio p xi
  have hz : ‖z‖ < 1 := routeAPrimePowerRatio_norm_lt_one p hp xi
  rw [show (∑' k : Nat, (routeAPrimePowerRatio p xi) ^ (k + 1)) =
      ∑' k : Nat, z ^ (k + 1) by rfl]
  rw [← geom_series_mul_shift z hz]
  rw [tsum_geometric_of_norm_lt_one hz]
  rfl

theorem routeAPrimePoissonSymbol_eq_primePowerExpansion
    (p : Nat) (hp : Nat.Prime p) (xi : Real) :
    routeAPrimePoissonSymbol p xi = routeAPrimePowerExpansion p xi := by
  let r : Real := 1 / Real.sqrt (p : Real)
  let theta : Real := Real.log (p : Real) * xi
  let z : Complex := routeAPrimePowerRatio p xi
  have hz : ‖z‖ < 1 := routeAPrimePowerRatio_norm_lt_one p hp xi
  have hclosed : (∑' k : Nat, z ^ (k + 1)) = z / (1 - z) := by
    simpa [z] using routeAPrimePowerExpansion_eq_geometric_closed_form p hp xi
  have hz_trig : z = (r : Complex) *
      (Complex.ofReal (Real.cos theta) +
        Complex.ofReal (Real.sin theta) * Complex.I) := by
    dsimp [z, r, theta, routeAPrimePowerRatio]
    rw [Complex.exp_mul_I]
    simp only [Complex.ofReal_cos, Complex.ofReal_sin]
  have hden : (1 - z).normSq =
      1 - 2 * r * Real.cos theta + r ^ 2 := by
    rw [hz_trig]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    ring_nf
    nlinarith [Real.sin_sq_add_cos_sq theta]
  have hden_pos : 0 < 1 - 2 * r * Real.cos theta + r ^ 2 := by
    have hne : (1 : Complex) - z ≠ 0 := by
      intro hzero
      have : z = 1 := (sub_eq_zero.mp hzero).symm
      rw [this] at hz
      simp at hz
    have hnorm : 0 < (1 - z).normSq := Complex.normSq_pos.mpr hne
    rw [hden] at hnorm
    exact hnorm
  have hreal : (z / (1 - z)).re =
      (r * Real.cos theta - r ^ 2) /
        (1 - 2 * r * Real.cos theta + r ^ 2) := by
    rw [Complex.div_re, hz_trig]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    have hden' :
        (1 - r * Real.cos theta) * (1 - r * Real.cos theta) +
            (0 - r * (0 + Real.sin theta * 1)) *
              (0 - r * (0 + Real.sin theta * 1)) =
          1 - 2 * r * Real.cos theta + r ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq theta]
    have hnum' :
        r * Real.cos theta * (1 - r * Real.cos theta) +
            r * (0 + Real.sin theta * 1) *
              (0 - r * (0 + Real.sin theta * 1)) =
          r * Real.cos theta - r ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq theta]
    rw [hden', ← add_div, hnum']
  unfold routeAPrimePowerExpansion
  rw [show (∑' k : Nat, (routeAPrimePowerRatio p xi) ^ (k + 1)) =
      ∑' k : Nat, z ^ (k + 1) by rfl, hclosed, hreal]
  unfold routeAPrimePoissonSymbol
  change (1 - r ^ 2) /
      (1 - 2 * r * Real.cos theta + r ^ 2) - 1 =
    2 * ((r * Real.cos theta - r ^ 2) /
      (1 - 2 * r * Real.cos theta + r ^ 2))
  have hden_ne : 1 - 2 * r * Real.cos theta + r ^ 2 ≠ 0 := ne_of_gt hden_pos
  have hden_inv :
      (1 - 2 * r * Real.cos theta + r ^ 2) *
          (1 - 2 * r * Real.cos theta + r ^ 2)⁻¹ = 1 :=
    mul_inv_cancel₀ hden_ne
  calc
    (1 - r ^ 2) /
          (1 - 2 * r * Real.cos theta + r ^ 2) - 1 =
        (1 - r ^ 2) *
            (1 - 2 * r * Real.cos theta + r ^ 2)⁻¹ -
          (1 - 2 * r * Real.cos theta + r ^ 2) *
            (1 - 2 * r * Real.cos theta + r ^ 2)⁻¹ := by
      rw [div_eq_mul_inv, hden_inv]
    _ = ((1 - r ^ 2) -
          (1 - 2 * r * Real.cos theta + r ^ 2)) *
        (1 - 2 * r * Real.cos theta + r ^ 2)⁻¹ := by ring
    _ = (2 * (r * Real.cos theta - r ^ 2)) *
        (1 - 2 * r * Real.cos theta + r ^ 2)⁻¹ := by ring
    _ = 2 * ((r * Real.cos theta - r ^ 2) /
        (1 - 2 * r * Real.cos theta + r ^ 2)) := by
      rw [div_eq_mul_inv]
      ring

end
end C1RouteAPrimePowerExpansion3127
end Source
end ConnesWeilRH
