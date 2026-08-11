import ConnesWeilRH.Dev.Wall14PlateauFDeriv
import ConnesWeilRH.Dev.Wall14PlateauExplicitF
import ConnesWeilRH.Dev.Wall14PlateauProbe

open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
namespace ConnesWeilRH.Source.Dev.Wall14Plateau

/-- A = integral bump^2, support in [-1,1], bump <= 1, so A <= 2. -/
lemma bumpA_le_two : bumpA <= (2 : ℝ) := by
  rw [bumpA_eq_integral_realSq]
  let g : ℝ → ℝ := fun t => (bumpReal t) ^ 2
  let h : ℝ → ℝ := fun t => (Set.Icc (-1 : ℝ) (1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) t
  have hqint : Integrable g := bumpSq_integrable
  have hmeas : MeasurableSet (Set.Icc (-1 : ℝ) (1 : ℝ)) := isClosed_Icc.measurableSet
  have hhin : (volume : Measure ℝ) (Set.Icc (-1 : ℝ) (1 : ℝ)) ≠ ⊤ := by rw [Real.volume_Icc]; norm_num
  have hhint : Integrable h := by
    rw [MeasureTheory.integrable_indicator_iff hmeas]
    exact MeasureTheory.integrableOn_const (C := (1 : ℝ)) (hC := by simp) hhin
  have hle : ∀ t : ℝ, g t <= h t := by
    intro t
    by_cases ht : |t| <= (1 : ℝ)
    · rcases abs_le.mp ht with ⟨h1, h2⟩
      have hIcc : t ∈ Set.Icc (-1 : ℝ) (1 : ℝ) := ⟨h1, h2⟩
      have hb : bumpReal t <= 1 := bumpReal_le_one t
      have hb2 : (bumpReal t) ^ 2 <= 1 := by nlinarith [bumpReal_nonneg t, hb]
      simp [g, h, hIcc, hb2]
    · have htt' : (1 : ℝ) < |t| := by by_contra hge; exact ht (le_of_not_gt hge)
      have hz : bumpReal t = 0 := bumpReal_eq_zero_of_abs_ge t (le_of_lt htt')
      have hnot : t ∉ Icc (-1 : ℝ) (1 : ℝ) := by
        intro hI; rcases hI with ⟨hl, hu⟩
        have hbnd : |t| <= 1 := abs_le.mpr ⟨hl, hu⟩
        nlinarith [htt', hbnd]
      simp [g, h, hz, hnot]
  have hmono : (∫ t : ℝ, g t) <= ∫ t : ℝ, h t := MeasureTheory.integral_mono hqint hhint hle
  have hmain : (∫ t : ℝ, h t) = (2 : ℝ) := by
    have hgi := MeasureTheory.integral_indicator_one (μ := (volume : Measure ℝ)) (s := Icc (-1 : ℝ) (1 : ℝ)) hmeas
    calc
      (∫ t : ℝ, h t) = (volume : Measure ℝ).real (Icc (-1 : ℝ) (1 : ℝ)) := by simpa [h] using hgi
      _ = 2 := by norm_num [Real.volume_Icc]
  exact hmono.trans_eq hmain

/-- e^{t} - 1 <= t * e^{1/2} for 0 <= t <= 1/2. -/
lemma exp_sub_one_le (t : ℝ) (ht0 : 0 <= t) (ht1 : t <= (1 / 2 : ℝ)) :
    Real.exp t - 1 <= t * Real.exp (1 / 2 : ℝ) := by
  have hFTC : (∫ x in (0 : ℝ)..t, Real.exp x) = Real.exp t - 1 := by
    have hI := intervalIntegral.integral_deriv_eq_sub' (a := (0 : ℝ)) (b := t)
      (f := fun x : ℝ => Real.exp x) (f' := fun x : ℝ => Real.exp x) (by simp)
      (fun x hx => (Real.hasDerivAt_exp x).differentiableAt)
      (by intro x hx; exact Real.continuous_exp.continuousAt x)
    rw [show (∫ x in (0 : ℝ)..t, Real.exp x) = Real.exp t - Real.exp 0 by simpa using hI, Real.exp_zero]
  have he_int : IntervalIntegrable (fun x : ℝ => Real.exp x) volume (0 : ℝ) t := (Real.continuous_exp).intervalIntegrable _ _
  have hc_int : IntervalIntegrable (fun _ : ℝ => Real.exp (1 / 2 : ℝ)) volume (0 : ℝ) t := (continuous_const).intervalIntegrable _ _
  have hmono : (∫ x in (0 : ℝ)..t, Real.exp x) <= ∫ x in (0 : ℝ)..t, Real.exp (1 / 2 : ℝ) := by
    exact intervalIntegral.integral_mono_on_of_le_Ioo (a := (0 : ℝ)) (b := t) ht0 he_int hc_int
      (by intro x hx; rw [Real.exp_le_exp]; linarith [ht1, hx.1, hx.2])
  have hconst : (∫ x in (0 : ℝ)..t, Real.exp (1 / 2 : ℝ)) = t * Real.exp (1 / 2 : ℝ) := by
    rw [intervalIntegral.integral_const]; ring
  calc
    Real.exp t - 1 = ∫ x in (0 : ℝ)..t, Real.exp x := by rw [hFTC]
    _ <= t * Real.exp (1 / 2 : ℝ) := by rw [← hconst]; exact hmono

/-- |e^{y/2} F(y) - A| <= y * (e^{1/2} + 1) on [0,1]. -/
lemma bumpN_abs_le_near (y : ℝ) (hy0 : 0 <= y) (hy1 : y <= 1) :
    |Real.exp (y / 2) * bumpF y - bumpA| <= y * (Real.exp (1 / 2 : ℝ) + 1) := by
  have hE : Real.exp (y / 2) - 1 <= (y / 2) * Real.exp (1 / 2 : ℝ) :=
    exp_sub_one_le (y / 2) (by positivity) (by linarith)
  have hEge : (0 : ℝ) <= Real.exp (y / 2) - 1 := by
    have hone : (1 : ℝ) <= Real.exp (y / 2) := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by positivity)
    linarith
  have hFle2 : |bumpF y| <= 2 := by
    have hFnn : 0 <= bumpF y := bumpF_nonneg y
    have hFup : bumpF y <= (2 : ℝ) := (bumpF_le_bumpA y).trans bumpA_le_two
    exact abs_le.mpr ⟨by linarith, hFup⟩
  have hAF : |bumpA - bumpF y| <= y := bumpA_sub_bumpF_le y hy0 hy1
  have hsplit : |Real.exp (y/2) * bumpF y - bumpA| <=
      (Real.exp (y / 2) - 1) * |bumpF y| + |bumpF y - bumpA| := by
    have h : Real.exp (y/2) * bumpF y - bumpA = (bumpF y * (Real.exp (y/2) - 1)) + (bumpF y - bumpA) := by ring
    calc
      |Real.exp (y/2) * bumpF y - bumpA| = |bumpF y * (Real.exp (y/2) - 1) + (bumpF y - bumpA)| := by rw [h]
      _ <= |bumpF y * (Real.exp (y/2) - 1)| + |bumpF y - bumpA| := abs_add_le _ _
      _ = (Real.exp (y/2) - 1) * |bumpF y| + |bumpF y - bumpA| := by rw [abs_mul, abs_of_nonneg hEge]; ring
  have hmain_term : (Real.exp (y / 2) - 1) * |bumpF y| <= (y / 2) * Real.exp (1 / 2 : ℝ) * 2 := by
    nlinarith [hE, hFle2, abs_nonneg (bumpF y)]
  have h_y : (y / 2) * Real.exp (1 / 2 : ℝ) * 2 = y * Real.exp (1 / 2 : ℝ) := by ring
  have hAbsAF : |bumpF y - bumpA| <= y := by
    calc
      |bumpF y - bumpA| = |bumpA - bumpF y| := abs_sub_comm _ _
      _ <= y := hAF
  nlinarith [hsplit, hmain_term, h_y, hAbsAF]

end ConnesWeilRH.Source.Dev.Wall14Plateau