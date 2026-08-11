import ConnesWeilRH.Dev.Wall14PlateauExplicitF
import ConnesWeilRH.Dev.Wall14PlateauFDeriv
import ConnesWeilRH.Dev.Wall14PlateauMidBand
open MeasureTheory Filter Set
open scoped Topology
namespace ConnesWeilRH.Source.Dev.Wall14Plateau

theorem bumpF_le_two_sub_y (y : ℝ) (hy0 : 0 <= y) (hy2 : y <= 2) : bumpF y <= 2 - y := by
  rw [bumpF_eq_conv]
  let S : Set ℝ := Set.Icc (y - 1) 1
  let I : ℝ → ℝ := S.indicator (fun _ : ℝ => (1 : ℝ))
  have hmeasS : MeasurableSet S := isClosed_Icc.measurableSet
  have hvolS : (volume : Measure ℝ) S ≠ ⊤ := by
    simp [S, Real.volume_Icc]
  have hII : Integrable I := by
    rw [MeasureTheory.integrable_indicator_iff hmeasS]
    exact MeasureTheory.integrableOn_const (C := (1 : ℝ)) (hC := by simp) hvolS
  have hProdn : Integrable (fun t : ℝ => bumpReal t * bumpReal (y - t)) := bumpRealMul_integrable y
  have hleq : ∀ t : ℝ, bumpReal t * bumpReal (y - t) <= I t := by
    intro t
    by_cases ht : t ∈ S
    · dsimp [I]; rw [Set.indicator_apply, if_pos ht]
      have hq1 : bumpReal t <= 1 := bumpReal_le_one t
      have hq2 : bumpReal (y - t) <= 1 := bumpReal_le_one (y - t)
      have ha : bumpReal t * bumpReal (y - t) <= bumpReal t * 1 :=
        mul_le_mul_of_nonneg_left hq2 (bumpReal_nonneg t)
      calc
        bumpReal t * bumpReal (y - t) <= bumpReal t * 1 := ha
        _ = bumpReal t := by ring
        _ <= 1 := hq1
    · dsimp [I]; rw [Set.indicator_apply, if_neg ht]
      have hG0 : bumpReal t * bumpReal (y - t) = 0 := by
        by_cases hBig : 1 < t
        · have hz : bumpReal t = 0 :=
            bumpReal_eq_zero_of_abs_ge t (by rw [abs_of_nonneg (by linarith)]; linarith)
          rw [hz]
          ring
        · have htle1 : t <= 1 := le_of_not_gt hBig
          have ht_small : t < y - 1 := by
            by_contra hzin
            have hge : y - 1 <= t := le_of_not_gt hzin
            exact ht ⟨hge, htle1⟩
          have hpos : 0 <= y - t := by linarith
          have hg1 : (1 : ℝ) <= |y - t| := by
            rw [abs_of_nonneg hpos]
            linarith
          have hz2 : bumpReal (y - t) = 0 := bumpReal_eq_zero_of_abs_ge (y - t) hg1
          rw [hz2]
          ring
      rw [hG0]
  have hmono : (∫ t : ℝ, bumpReal t * bumpReal (y - t)) <= ∫ t : ℝ, I t :=
    MeasureTheory.integral_mono hProdn hII hleq
  have hIint : (∫ t : ℝ, I t) = (2 - y) := by
    have hgi := MeasureTheory.integral_indicator_one (μ := (volume : Measure ℝ)) (s := S) hmeasS
    calc
      (∫ t : ℝ, I t) = (volume : Measure (ℝ)).real S := by simpa [I] using hgi
      _ = 2 - y := by
        have hm0 : 0 <= (1 : ℝ) - (y - 1) := by linarith
        simp [S, Real.volume_Icc, max_eq_left hm0]
        ring
  exact hmono.trans_eq hIint

/-- `e^{1/2} < 9/5`, via `e < (9/5)^2`. -/
lemma bump_ehalf_lt_ninths : Real.exp (1 / 2 : ℝ) < (9 / 5 : ℝ) := by
  have hsq : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp (1 : ℝ) := by
    rw [pow_two]
    rw [← Real.exp_add]
    norm_num
  have he1 : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three
  have h3 : (3 : ℝ) < (9 / 5 : ℝ) ^ 2 := by norm_num
  have hlt : (Real.exp (1 / 2 : ℝ)) ^ 2 < (9 / 5 : ℝ) ^ 2 := by
    rw [hsq]
    exact lt_trans he1 h3
  have hSq : |Real.exp (1 / 2 : ℝ)| < |(9 / 5 : ℝ)| := sq_lt_sq.mp hlt
  have ha : |Real.exp (1 / 2 : ℝ)| = Real.exp (1 / 2 : ℝ) :=
    abs_of_nonneg (le_of_lt (Real.exp_pos (1 / 2 : ℝ)))
  have hb : |(9 / 5 : ℝ)| = (9 / 5 : ℝ) := abs_of_nonneg (by norm_num)
  rwa [ha, hb] at hSq



/-! ### Mid band: decay constant, sign (N<=0), exponential abs bound. -/

/-- `e^{y/2}*(2-y) <= e^{1/2}` for `1<=y<=2`. -/
lemma bump_decay_down (y : ℝ) (hy1 : 1 <= y) (hy2 : y <= 2) :
    Real.exp (y / 2) * (2 - y) <= Real.exp (1 / 2 : ℝ) := by
  have hline : 2 - y <= Real.exp ((1 - y) / 2) := by
    have ha : 1 + (1 - y) / 2 <= Real.exp ((1 - y) / 2) := by
      simpa [add_comm] using (Real.add_one_le_exp ((1 - y) / 2))
    have hb : 2 - y <= 1 + (1 - y) / 2 := by
      apply sub_nonneg.mp
      have hsub : (1 + (1 - y) / 2) - (2 - y) = (y - 1) / 2 := by ring_nf
      rw [hsub]
      positivity
    exact hb.trans ha
  have h_ey : 0 < Real.exp (y / 2) := Real.exp_pos (y / 2)
  calc
    Real.exp (y / 2) * (2 - y) = (2 - y) * Real.exp (y / 2) := by ring
    _ <= Real.exp ((1 - y) / 2) * Real.exp (y / 2) :=
      mul_le_mul_of_nonneg_right hline (le_of_lt h_ey)
    _ = Real.exp ((1 - y) / 2 + y / 2) := by rw [Real.exp_add]
    _ = Real.exp (1 / 2 : ℝ) := by ring_nf

/-- `e^{y/2}*bumpF y <= e^{1/2}` for `1<=y<=2`. -/
lemma bump_expHalfF_le_small (y : ℝ) (hy1 : 1 <= y) (hy2 : y <= 2) :
    Real.exp (y / 2) * bumpF y <= Real.exp (1 / 2 : ℝ) := by
  have hy0 : 0 <= y := by linarith
  have hF : bumpF y <= 2 - y := bumpF_le_two_sub_y y hy0 hy2
  have hdec := bump_decay_down y hy1 hy2
  have hepos : 0 <= Real.exp (y / 2) := le_of_lt (Real.exp_pos (y / 2))
  calc
    Real.exp (y / 2) * bumpF y <= Real.exp (y / 2) * (2 - y) :=
      mul_le_mul_of_nonneg_left hF hepos
    _ <= Real.exp (1 / 2 : ℝ) := hdec

/-- `e^{y/2}*F(y) <= bumpA` on `[1,2]` (mid sign). -/
theorem bump_expHalfF_le_A (y : ℝ) (hy1 : 1 <= y) (hy2 : y <= 2) :
    Real.exp (y / 2) * bumpF y <= bumpA := by
  have hsmall := bump_expHalfF_le_small y hy1 hy2
  have hen : Real.exp (1 / 2 : ℝ) <= bumpA := by
    exact (le_of_lt bump_ehalf_lt_ninths).trans bumpA_ge_nine_fifths
  exact hsmall.trans hen

/-- `|e^{y/2}*F - A| <= A` on `[1,2]`. -/
lemma bump_abs_numerId (y : ℝ) (hy1 : 1 <= y) (hy2 : y <= 2) :
    |Real.exp (y / 2) * bumpF y - bumpA| <= bumpA := by
  have hnpos : Real.exp (y / 2) * bumpF y - bumpA <= 0 := by
    have hn := bump_expHalfF_le_A y hy1 hy2
    linarith
  have hnneg : -bumpA <= Real.exp (y / 2) * bumpF y - bumpA := by
    have hE : 0 <= Real.exp (y / 2) * bumpF y :=
      mul_nonneg (le_of_lt (Real.exp_pos (y / 2))) (bumpF_nonneg y)
    linarith
  exact abs_le.mpr ⟨hnneg, hnpos.trans (le_of_lt bumpA_pos)⟩

/-- `1/den(y) <= e^{-y}/(1-e^{-2})` for `y >= 1`. -/
theorem den_inv_le_exp (y : ℝ) (hy : 1 <= y) :
    ((1 : ℝ) / den y) <= (Real.exp (-y) / (1 - Real.exp (-2 : ℝ))) := by
  have hdenpos : 0 < den y := den_pos y (by linarith)
  have hcpos : 0 < (1 : ℝ) - Real.exp (-2 : ℝ) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hden1 : Real.exp (-y) * den y = 1 - Real.exp (-(2 * y)) := by
    unfold den
    rw [mul_sub]
    rw [show Real.exp (-y) * Real.exp y = 1 by
      rw [← Real.exp_add, show (-y) + y = 0 by ring, Real.exp_zero]]
    rw [show Real.exp (-y) * Real.exp (-y) = Real.exp (-(2 * y)) by
      rw [← Real.exp_add, show (-y) + (-y) = -(2 * y) by ring]]
  have heq : Real.exp (-(2 * y)) <= Real.exp (-2 : ℝ) :=
    Real.exp_le_exp.mpr (by linarith)
  have hneg : -(Real.exp (-2 : ℝ)) <= -(Real.exp (-(2 * y))) := by linarith
  have hcross : (1 - Real.exp (-2 : ℝ)) <= Real.exp (-y) * den y := by
    rw [hden1]
    nlinarith
  have hden_ne : den y ≠ 0 := ne_of_gt hdenpos
  have hcz : (1 - Real.exp (-2 : ℝ)) ≠ 0 := ne_of_gt hcpos
  rw [div_le_iff₀ hdenpos]
  field_simp [hden_ne, hcz, Real.exp_ne_zero]
  nlinarith [mul_le_mul_of_nonneg_left hcross (by norm_num : (0 : ℝ) <= 1)]
/-- `|bumpArchG y| <= 2A e^{-y}/(1-e^{-2})` on `[1,2]`. -/
theorem bumpG_abs_mid_exp (y : ℝ) (hy1 : 1 <= y) (hy2 : y <= 2) :
    |bumpArchG y| <= (2 * bumpA) * (Real.exp (-y) / (1 - Real.exp (-2 : ℝ))) := by
  have hypos : 0 < y := by linarith
  have hden : 0 < den y := den_pos y hypos
  have hN : |Real.exp (y / 2) * bumpF y - bumpA| <= bumpA := bump_abs_numerId y hy1 hy2
  have hA0 : 0 <= 2 * bumpA := mul_nonneg (by norm_num) (le_of_lt bumpA_pos)
  have hBle : 2 * |Real.exp (y/2)*bumpF y - bumpA| <= 2 * bumpA := by
    nlinarith [hN]
  have hprod : (2 * bumpA) / den y <= (2 * bumpA) * (Real.exp (-y) / (1 - Real.exp (-2 : ℝ))) := by
    calc
      (2 * bumpA) / den y = (2 * bumpA) * (1 / den y) := by
        rw [div_eq_mul_one_div]
      _ <= (2 * bumpA) * (Real.exp (-y) / (1 - Real.exp (-2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (den_inv_le_exp y hy1) hA0
  unfold bumpArchG
  rw [bumpArchimedeanNumeratorRe_eq_two_G]
  rw [abs_div, abs_mul]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) <= 2)]
  rw [abs_of_pos hden]
  calc
    (2 * |Real.exp (y/2)*bumpF y - bumpA|) / den y
        <= (2 * bumpA) / den y := by
      exact div_le_div_of_nonneg_right hBle (le_of_lt hden)
    _ <= (2 * bumpA) * (Real.exp (-y) / (1 - Real.exp (-2 : ℝ))) := hprod
end Wall14Plateau
end Dev
end Source
end ConnesWeilRH