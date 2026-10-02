import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
import ConnesWeilRH.Dev.C1RouteAPanelQuadrature2457
import ConnesWeilRH.Dev.C1RouteAIntervalAlgebra
import ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
import ConnesWeilRH.Dev.C1RouteAExternalOwnerIdentity

/-  2459: the W-C attachment layer for the quadrature import
(obligations of records 2455/2458).  All statements are generic in the
panel data; the producer (targeting the 2338 balls per record 2456)
supplies the boxes and bounds.  Contents:

- widthBump half-line monotonicity (the bump box shape);
- cos/sin 1-Lipschitz and midpoint-box lemmas (the phase box shape);
- the family panel door: factor boxes over a panel bound the family
  value at every panel point (the A7-safe composed hull);
- the 30-family sum panel door (mem_sumFinset, one line);
- the trapezoid-upper-bound corollary of the 2457 panel theorem (the
  node/ζ attachment interface);
- the support glue: stripNorm equals the interval integral for
  supported integrands (the 2343 discharge interface).

Owner-independent: every box and bound is a hypothesis.  -/

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-  bump box shape: the bump is antitone on the positive half of the
support and monotone on the negative half (it depends on the position
only through the square).  -/

theorem widthBump_antitone_right_2459 (radius : ℝ) :
    AntitoneOn (C1RouteAOwnerScaleAudit.widthBump radius) (Set.Ico 0 radius) := by
  intro x hx y hy hxy
  have hr0 : (0:ℝ) < radius := by
    have h1 := (Set.mem_Ico.mp hx).2
    linarith [(Set.mem_Ico.mp hx).1]
  have hx0 : 0 ≤ x := (Set.mem_Ico.mp hx).1
  have hy0 : 0 ≤ y := (Set.mem_Ico.mp hy).1
  have hxin : |x| < radius := by rw [abs_of_nonneg hx0]; exact (Set.mem_Ico.mp hx).2
  have hyin : |y| < radius := by rw [abs_of_nonneg hy0]; exact (Set.mem_Ico.mp hy).2
  unfold C1RouteAOwnerScaleAudit.widthBump
  rw [if_pos hxin, if_pos hyin]
  apply Real.exp_le_exp.mpr
  --  x ≤ y in [0, radius)  =>  (y/r)^2 ≥ (x/r)^2  =>  q_y ≤ q_x
  have hsq : x ^ 2 ≤ y ^ 2 := by nlinarith [hx0, hy0, hxy]
  have hr2 : (0:ℝ) < radius ^ 2 := by nlinarith
  have hqxy : (1:ℝ) - (y / radius) ^ 2 ≤ 1 - (x / radius) ^ 2 := by
    have h1 : (x / radius) ^ 2 = x ^ 2 / radius ^ 2 := by field_simp
    have h2 : (y / radius) ^ 2 = y ^ 2 / radius ^ 2 := by field_simp
    rw [h1, h2]
    field_simp
    linarith
  have hqy : (0:ℝ) < 1 - (y / radius) ^ 2 := by
    have h1 : (y / radius) ^ 2 < 1 := by
      have hp := abs_lt.mp hyin
      have hsq2 : y ^ 2 < radius ^ 2 := by nlinarith [hp.1, hp.2]
      have h3 : (y / radius) ^ 2 = y ^ 2 / radius ^ 2 := by field_simp
      rw [h3]
      field_simp
      linarith
    linarith
  have hqx : (0:ℝ) < 1 - (x / radius) ^ 2 := by
    have h1 : (x / radius) ^ 2 < 1 := by
      have hp := abs_lt.mp hxin
      have hsq2 : x ^ 2 < radius ^ 2 := by nlinarith [hp.1, hp.2]
      have h3 : (x / radius) ^ 2 = x ^ 2 / radius ^ 2 := by field_simp
      rw [h3]
      field_simp
      linarith
    linarith
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact (div_le_div_iff_of_pos_left (by norm_num) hqx hqy).mpr hqxy

theorem widthBump_mono_left_2459 (radius : ℝ) :
    MonotoneOn (C1RouteAOwnerScaleAudit.widthBump radius) (Set.Ioc (-radius) 0) := by
  intro x hx y hy hxy
  have hxr : -radius < x := (Set.mem_Ioc.mp hx).1
  have hx0 : x ≤ 0 := (Set.mem_Ioc.mp hx).2
  have hyr : -radius < y := (Set.mem_Ioc.mp hy).1
  have hy0 : y ≤ 0 := (Set.mem_Ioc.mp hy).2
  have hr0 : (0:ℝ) < radius := by linarith
  have hxin : |x| < radius := by rw [abs_of_nonpos hx0]; linarith
  have hyin : |y| < radius := by rw [abs_of_nonpos hy0]; linarith
  unfold C1RouteAOwnerScaleAudit.widthBump
  rw [if_pos hxin, if_pos hyin]
  apply Real.exp_le_exp.mpr
  --  x ≤ y in (-radius, 0]  =>  (y/r)^2 ≤ (x/r)^2  =>  q_x ≤ q_y
  have hsq : y ^ 2 ≤ x ^ 2 := by nlinarith [hxy, hy0]
  have hr2 : (0:ℝ) < radius ^ 2 := by nlinarith
  have hq : (1:ℝ) - (x / radius) ^ 2 ≤ 1 - (y / radius) ^ 2 := by
    have h1 : (x / radius) ^ 2 = x ^ 2 / radius ^ 2 := by field_simp
    have h2 : (y / radius) ^ 2 = y ^ 2 / radius ^ 2 := by field_simp
    rw [h1, h2]
    field_simp
    linarith
  have hqx : (0:ℝ) < 1 - (x / radius) ^ 2 := by
    have h1 : (x / radius) ^ 2 < 1 := by
      have hp := abs_lt.mp hxin
      have hsq2 : x ^ 2 < radius ^ 2 := by nlinarith [hp.1, hp.2]
      have h3 : (x / radius) ^ 2 = x ^ 2 / radius ^ 2 := by field_simp
      rw [h3]
      field_simp
      linarith
    linarith
  have hqy : (0:ℝ) < 1 - (y / radius) ^ 2 := by
    have h1 : (y / radius) ^ 2 < 1 := by
      have hp := abs_lt.mp hyin
      have hsq2 : y ^ 2 < radius ^ 2 := by nlinarith [hp.1, hp.2]
      have h3 : (y / radius) ^ 2 = y ^ 2 / radius ^ 2 := by field_simp
      rw [h3]
      field_simp
      linarith
    linarith
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact (div_le_div_iff_of_pos_left (by norm_num) hqy hqx).mpr hq

/-  phase box shape: cos and sin are 1-Lipschitz, so the value at any
panel point sits in the midpoint box of half width.  -/

theorem cos_lipschitz_2459 (u v : ℝ) :
    |Real.cos u - Real.cos v| ≤ |u - v| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := Real.cos) (C := (1:ℝ))
    (fun x _ => Real.differentiable_cos x)
    (fun x _ => by
      rw [Real.deriv_cos, norm_neg, Real.norm_eq_abs]
      exact Real.abs_sin_le_one x)
    convex_univ (Set.mem_univ u) (Set.mem_univ v)
  simpa [Real.norm_eq_abs, abs_sub_comm] using h

theorem sin_lipschitz_2459 (u v : ℝ) :
    |Real.sin u - Real.sin v| ≤ |u - v| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := Real.sin) (C := (1:ℝ))
    (fun x _ => Real.differentiable_sin x)
    (fun x _ => by
      rw [Real.deriv_sin, Real.norm_eq_abs]
      exact Real.abs_cos_le_one x)
    convex_univ (Set.mem_univ u) (Set.mem_univ v)
  simpa [Real.norm_eq_abs, abs_sub_comm] using h

theorem cos_midpoint_box_2459 {t0 t1 u : ℝ} (h01 : t0 ≤ t1) (hu : u ∈ Set.Icc t0 t1) :
    |Real.cos u - Real.cos ((t0 + t1) / 2)| ≤ (t1 - t0) / 2 := by
  have hu1 : t0 ≤ u := hu.1
  have hu2 : u ≤ t1 := hu.2
  have hlo : -((t1 - t0) / 2) ≤ u - (t0 + t1) / 2 := by linarith
  have hhi : u - (t0 + t1) / 2 ≤ (t1 - t0) / 2 := by linarith
  refine le_trans (cos_lipschitz_2459 u ((t0 + t1) / 2)) (abs_le.mpr ?_)
  exact ⟨hlo, hhi⟩

theorem sin_midpoint_box_2459 {t0 t1 u : ℝ} (h01 : t0 ≤ t1) (hu : u ∈ Set.Icc t0 t1) :
    |Real.sin u - Real.sin ((t0 + t1) / 2)| ≤ (t1 - t0) / 2 := by
  have hu1 : t0 ≤ u := hu.1
  have hu2 : u ≤ t1 := hu.2
  have hlo : -((t1 - t0) / 2) ≤ u - (t0 + t1) / 2 := by linarith
  have hhi : u - (t0 + t1) / 2 ≤ (t1 - t0) / 2 := by linarith
  refine le_trans (sin_lipschitz_2459 u ((t0 + t1) / 2)) (abs_le.mpr ?_)
  exact ⟨hlo, hhi⟩

/-  the family panel door: with the bump, cos, and sin boxes over a
panel (the bump box required to straddle zero, as the producer's clamped
boxes do), the composed hull bounds the family value at every panel
point - inside and outside the family support alike.  -/

theorem familyPanelMem_2459 (coefficient : ℂ) {radius modulation x0 x1 :
  ℝ} {bumpLo bumpHi cosLo cosHi sinLo sinHi : ℝ}
    (hzero : bumpLo ≤ 0 ∧ 0 ≤ bumpHi)
    (hbump : ∀ x ∈ Set.Icc x0 x1,
      bumpLo ≤ C1RouteAOwnerScaleAudit.widthBump radius x ∧
        C1RouteAOwnerScaleAudit.widthBump radius x ≤ bumpHi)
    (hcos : ∀ x ∈ Set.Icc x0 x1,
      cosLo ≤ Real.cos (modulation * x) ∧
        Real.cos (modulation * x) ≤ cosHi)
    (hsin : ∀ x ∈ Set.Icc x0 x1,
      sinLo ≤ Real.sin (modulation * x) ∧
        Real.sin (modulation * x) ≤ sinHi)
    (x : ℝ) (hx : x ∈ Set.Icc x0 x1) :
    (ComplexRect2427.mul
      (ComplexRect2427.mul (ComplexRect2427.point coefficient)
        { reLo := bumpLo, reHi := bumpHi, imLo := 0, imHi := 0 })
      { reLo := cosLo, reHi := cosHi, imLo := sinLo, imHi := sinHi }).Mem
      (externalFamilyValue2344 coefficient modulation radius x) := by
  rw [externalFamilyValue2344_eq_familyTerm]
  have hbm : ({ reLo := bumpLo, reHi := bumpHi, imLo := 0, imHi := 0 } :
      ComplexRect2427).Mem (C1RouteAOwnerScaleAudit.widthBump radius x : ℂ) := by
    by_cases hinside : |x| < radius
    · have hb := hbump x hx
      refine ⟨?_, ?_, le_refl 0, le_refl 0⟩
      · simpa [Complex.ofReal_re] using hb.1
      · simpa [Complex.ofReal_re] using hb.2
    · have hb0 : C1RouteAOwnerScaleAudit.widthBump radius x = 0 := by
        simp [C1RouteAOwnerScaleAudit.widthBump, hinside]
      refine ⟨?_, ?_, le_refl 0, le_refl 0⟩
      · simpa [Complex.ofReal_re, hb0] using hzero.1
      · simpa [Complex.ofReal_re, hb0] using hzero.2
  have hph : ({ reLo := cosLo, reHi := cosHi, imLo := sinLo, imHi := sinHi } :
      ComplexRect2427).Mem
      (Complex.exp ((modulation * x : ℝ) * Complex.I)) := by
    have hre : (Complex.exp ((modulation * x : ℝ) * Complex.I)).re
        = Real.cos (modulation * x) := by
      rw [Complex.exp_re]
      simp
    have him : (Complex.exp ((modulation * x : ℝ) * Complex.I)).im
        = Real.sin (modulation * x) := by
      rw [Complex.exp_im]
      simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hre]; exact (hcos x hx).1
    · rw [hre]; exact (hcos x hx).2
    · rw [him]; exact (hsin x hx).1
    · rw [him]; exact (hsin x hx).2
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.mem_mul (ComplexRect2427.point_mem coefficient) hbm) hph

/-  the 30-family sum panel door.  -/

theorem sumPanelMem_2459 {x0 x1 : ℝ} {radii : Fin 30 → ℝ}
    {coefficients : Fin 30 → ℂ} {modulations : Fin 30 → ℝ}
    (rect : Fin 30 → ComplexRect2427)
    (hFam : ∀ i : Fin 30, ∀ x ∈ Set.Icc x0 x1,
      (rect i).Mem
        (externalFamilyValue2344 (coefficients i) (modulations i) (radii i) x))
    (x : ℝ) (hx : x ∈ Set.Icc x0 x1) :
    (ComplexRect2427.sumFinset rect Finset.univ).Mem
      (∑ i : Fin 30,
        externalFamilyValue2344 (coefficients i) (modulations i) (radii i) x) :=
  ComplexRect2427.mem_sumFinset fun i _ => hFam i x hx

/-  node/ζ attachment interface: an upper bound T on the trapezoidal
sum turns the 2457 panel theorem into the discharge shape.  -/

theorem panelQuadrature_le_of_trapLe_2459 {g : ℝ → ℝ} {a b ζ T : ℝ}
    {N : ℕ} (hN : 0 < N) (hab : a ≤ b)
    (h_c2 : ContDiffOn ℝ 2 g (Set.uIcc a b))
    (hζ : ∀ x, |iteratedDerivWithin 2 g (Set.uIcc a b) x| ≤ ζ)
    (htrap : trapezoidal_integral g N a b ≤ T) :
    ∫ x in a..b, g x ≤ T + (b - a) ^ 3 * ζ / (12 * N ^ 2) :=
  le_trans (panelQuadrature_le_2457 hN hab h_c2 hζ) (by linarith)

/-  support glue: the full-line strip norm equals the interval
integral whenever the integrand is supported in the closed interval.  -/

theorem stripNorm_eq_interval_2459 (F : ℝ → ℂ) (σ a b : ℝ)
    (hsupp : Function.support (fun x => Real.exp (σ * x) * ‖F x‖) ⊆
      Set.Ioc a b) :
    stripNorm σ F = ∫ x in a..b, Real.exp (σ * x) * ‖F x‖ := by
  unfold stripNorm
  rw [intervalIntegral.integral_eq_integral_of_support_subset hsupp]

end ConnesWeilRH.Dev
