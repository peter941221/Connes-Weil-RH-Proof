import ConnesWeilRH.Dev.Wall14PlateauExplicitF
import ConnesWeilRH.Dev.Wall14PlateauFDeriv
import ConnesWeilRH.Dev.Wall14PlateauNear
import ConnesWeilRH.Dev.Wall14PlateauIntegrateH
import ConnesWeilRH.Dev.Wall14CoeffBound
import ConnesWeilRH.Source.CCM25Concrete.SelectedArchimedeanIntegrability
import ConnesWeilRH.Dev.Wall14ArchSufficiency

/-!
Wall-A 1.4 ``hI`` closure at the explicit big-plateau bump owner.
Near/mid/tail integral pieces of ``|bumpArchG|`` on ``(0,inf)`` so that
``|INT_0^inf (Re integrand)| <= 11/4 + A < C*A`` where
``C = log(4pi)+gamma``, ``A = bumpA``.  The bump is the explicit ``bumpEx``
(plateau ``1`` on ``[-9/10,9/10]``, support radius ``1``).  RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace Wall14Plateau

open MeasureTheory
open scoped Topology
open Filter Set
open scoped ComplexConjugate
open ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare
open ConnesWeilRH.Source.CCM25Concrete.SelectedWeilSquare.SelectedWeilSquareOwner

/-! ### A <= 2 (support in [-1,1], 0<=bumpReal<=1) -/

lemma bumpA_le_two : bumpA <= (2 : ℝ) := by
  rw [bumpA_eq_integral_realSq]
  let g : ℝ → ℝ := fun t => (bumpReal t) ^ 2
  let h : ℝ → ℝ := fun t => (Set.Icc (-1 : ℝ) (1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) t
  have hqint : Integrable g := bumpSq_integrable
  have hmeas : MeasurableSet (Set.Icc (-1 : ℝ) (1 : ℝ)) := isClosed_Icc.measurableSet
  have hhin : (volume : Measure ℝ) (Set.Icc (-1 : ℝ) (1 : ℝ)) ≠ ⊤ := by
    rw [Real.volume_Icc]; norm_num
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

/-! ### Near band (0,1]: slope control of the removable singularity. -/

/-- ``e^{t}-1 <= t*e^{1/2}`` for ``0<=t<=1/2``. -/
lemma exp_sub_one_le (t : ℝ) (ht0 : 0 <= t) (ht1 : t <= (1 / 2 : ℝ)) :
    Real.exp t - 1 <= t * Real.exp (1 / 2 : ℝ) := by
  have hFTC : (∫ x in (0 : ℝ)..t, Real.exp x) = Real.exp t - 1 := by
    have hI : (∫ y in (0 : ℝ)..t, deriv (fun x : ℝ => Real.exp x) y) = Real.exp t - Real.exp 0 :=
      (intervalIntegral.integral_deriv_eq_sub (a := (0 : ℝ)) (b := t) (f := fun x : ℝ => Real.exp x)
        (by intro x hx; exact (Real.hasDerivAt_exp x).differentiableAt)
        (by simpa [Real.deriv_exp] using (Real.continuous_exp).intervalIntegrable (0 : ℝ) t))
    simpa [Real.deriv_exp, Real.exp_zero] using hI
  have he_int : IntervalIntegrable (fun x : ℝ => Real.exp x) volume (0 : ℝ) t := (Real.continuous_exp).intervalIntegrable _ _
  have hc_int : IntervalIntegrable (fun _ : ℝ => Real.exp (1 / 2 : ℝ)) volume (0 : ℝ) t :=
    (continuous_const).intervalIntegrable _ _
  have hmono : (∫ x in (0 : ℝ)..t, Real.exp x) <= ∫ x in (0 : ℝ)..t, Real.exp (1 / 2 : ℝ) := by
    exact intervalIntegral.integral_mono_on_of_le_Ioo (a := (0 : ℝ)) (b := t) ht0 he_int hc_int
      (by intro x hx; rw [Real.exp_le_exp]; linarith [ht1, hx.1, hx.2])
  have hconst : (∫ x in (0 : ℝ)..t, Real.exp (1 / 2 : ℝ)) = t * Real.exp (1 / 2 : ℝ) := by
    rw [intervalIntegral.integral_const]; ring
  calc
    Real.exp t - 1 = ∫ x in (0 : ℝ)..t, Real.exp x := by rw [hFTC]
    _ <= t * Real.exp (1 / 2 : ℝ) := by rw [← hconst]; exact hmono

/-- ``|e^{y/2}F(y)-A| <= y*(e^{1/2}+1)`` on ``[0,1]``. -/
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

/-- ``|bumpArchG y| <= e^{1/2}+1`` on ``[0,1]``. -/
theorem bumpG_abs_le_near (y : ℝ) (hy0 : 0 <= y) (hy1 : y <= 1) :
    |bumpArchG y| <= Real.exp (1 / 2 : ℝ) + 1 := by
  let Q : ℝ := Real.exp (1 / 2 : ℝ) + 1
  by_cases hyz : y = 0
  · subst y
    have hnum : bumpPlateauOwner.archimedeanNumeratorRe 0 = 0 := by
      rw [bumpArchimedeanNumeratorRe_eq_two_G]
      rw [bumpF_zero_eq_bumpA]
      norm_num
    unfold bumpArchG
    rw [hnum]
    have hval : 0 / den 0 = 0 := by simp
    rw [hval]
    simp
    positivity
  · have hypos : 0 < y := lt_of_le_of_ne hy0 (by intro h; exact hyz h.symm)
    have hden : 0 < den y := den_pos y hypos
    have hN : |Real.exp (y / 2) * bumpF y - bumpA| <= y * (Real.exp (1 / 2 : ℝ) + 1) :=
      bumpN_abs_le_near y hy0 hy1
    unfold bumpArchG
    rw [bumpArchimedeanNumeratorRe_eq_two_G]
    have hnumA : |2 * (Real.exp (y / 2) * bumpF y - bumpA) / den y| <= Real.exp (1 / 2 : ℝ) + 1 := by
      have h2n : |2 * (Real.exp (y/2)*bumpF y - bumpA)| = 2 * |Real.exp (y/2)*bumpF y - bumpA| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) <= (2:ℝ))]
      rw [abs_div]
      rw [h2n]
      rw [abs_of_pos hden]
      have hle : 2 * |Real.exp (y/2)*bumpF y - bumpA| / den y <= Real.exp (1 / 2 : ℝ) + 1 := by
        rw [div_le_iff₀ hden]
        have hQ : (0:ℝ) <= Real.exp (1 / 2 : ℝ) + 1 := by positivity
        have hA : 2 * |Real.exp (y/2)*bumpF y - bumpA| <= (2 * y) * (Real.exp (1 / 2 : ℝ) + 1) := by
          nlinarith [hN]
        have hB : (2 * y) * (Real.exp (1 / 2 : ℝ) + 1) <= den y * (Real.exp (1 / 2 : ℝ) + 1) := by
          exact mul_le_mul_of_nonneg_right (deny_ge_two y hy0) hQ
        nlinarith [hA, hB]
      exact hle
    exact hnumA

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


/-! ### Integral assembly on (0,inf): |Re-integral| <= integral |g| -/

/-- Whole pointwise upper bound on the tail-y half line: `|g| <= 2A e^{-y}/(1-e^{-2})`. -/
lemma bump_whole_exp (y : Real) (h1 : 1 <= y) :
    |bumpArchG y| <= (2 * bumpA) * (Real.exp (-y) / (1 - Real.exp (-2 : Real))) := by
  have hA0 : 0 <= 2 * bumpA := mul_nonneg (by norm_num) (le_of_lt bumpA_pos)
  by_cases h2 : y <= 2
  · exact bumpG_abs_mid_exp y h1 h2
  · have hy2 : 2 < y := lt_of_not_ge h2
    have htail : |bumpArchG y| = 2 * bumpA / den y := bumpG_abs_tail y (le_of_lt hy2)
    have hd := den_inv_le_exp y h1
    rw [htail]
    calc
      2 * bumpA / den y = (2 * bumpA) * (1 / den y) := by rw [div_eq_mul_one_div]
      _ <= (2 * bumpA) * (Real.exp (-y) / (1 - Real.exp (-2 : Real))) :=
        mul_le_mul_of_nonneg_left hd hA0

/-- `norm (integrand y) = |g(y)|` on `y>0`. -/
lemma bump_norm_integrand_eq_abs (y : Real) (hy : 0 < y) :
    ‖bumpPlateauOwner.archimedeanIntegrand y‖ = |bumpArchG y| := by
  have heq : bumpPlateauOwner.archimedeanIntegrand y = (bumpArchG y : Complex) := by
    apply Complex.ext
    · simp [archimedeanIntegrand_re_eq_bumpArchG y hy]
    · simpa using bumpPlateauOwner.archimedeanIntegrand_im_eq_zero y
  rw [heq]
  simp

/-! |Re(integral)| <= integral |g| on (0,inf). -/
lemma bump_abs_re_int_Ioi_le :
    |(∫ y in Ioi (0 : Real), bumpPlateauOwner.archimedeanIntegrand y).re|
      <= ∫ y in Ioi (0 : Real), |bumpArchG y| := by
  let mu : Measure Real := volume.restrict (Ioi (0 : Real))
  have hmeas0 : MeasurableSet (Ioi (0 : Real)) := isOpen_Ioi.measurableSet
  have hchain : |(∫ y : Real, bumpPlateauOwner.archimedeanIntegrand y ∂mu).re|
          <= ∫ y : Real, |bumpArchG y| ∂mu := by
    calc
      |(∫ y : Real, bumpPlateauOwner.archimedeanIntegrand y ∂mu).re|
          <= ‖∫ y : Real, bumpPlateauOwner.archimedeanIntegrand y ∂mu‖ := Complex.abs_re_le_norm _
      _ <= ∫ y : Real, ‖bumpPlateauOwner.archimedeanIntegrand y‖ ∂mu :=
            MeasureTheory.norm_integral_le_integral_norm (fun y : Real => bumpPlateauOwner.archimedeanIntegrand y)
      _ = ∫ y : Real, |bumpArchG y| ∂mu := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [MeasureTheory.self_mem_ae_restrict hmeas0] with y hy
            have hy0 : 0 < y := by simpa using hy
            exact bump_norm_integrand_eq_abs y hy0
  change |(∫ y : Real, bumpPlateauOwner.archimedeanIntegrand y ∂mu).re| <=
            ∫ y : Real, |bumpArchG y| ∂mu
  exact hchain

/-! ### Integral assembly on (0,inf): |Re(Int)| <= Int |g| <= 11/4 + (4/3) A -/

/-- `|g|` integrable on `(0,inf)`, since it equals the norm of the integrand there. -/
theorem bump_integrable_Ioi_abs :
    IntegrableOn (fun y : Real => |bumpArchG y|) (Ioi (0 : Real)) := by
  have h0 : Integrable (fun y : Real => ‖bumpPlateauOwner.archimedeanIntegrand y‖)
      (volume.restrict (Ioi (0 : Real))) :=
    MeasureTheory.Integrable.norm bumpPlateauOwner.archimedeanIntegrand_integrableOn_Ioi
  have hEq : (fun y : Real => |bumpArchG y|) =ᵐ[volume.restrict (Ioi (0 : Real))]
      (fun y : Real => ‖bumpPlateauOwner.archimedeanIntegrand y‖) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict (isOpen_Ioi.measurableSet)] with y hy
    exact (bump_norm_integrand_eq_abs y (by simpa using hy)).symm
  exact h0.congr hEq.symm

/-! ### Near-band integral on (0,1] -/

/- `|g|` integrable on (0,1]. -/
lemma bump_integrableOn_Ioc01_abs :
    IntegrableOn (fun y : Real => |bumpArchG y|) (Ioc (0 : Real) 1) := by
  exact bump_integrable_Ioi_abs.mono_set (by
    intro y hy
    simp at hy
    exact hy.1)

/- `|g|` integrable on (1,inf). -/
lemma bump_integrableOn_Ioi1_abs :
    IntegrableOn (fun y : Real => |bumpArchG y|) (Ioi (1 : Real)) := by
  exact bump_integrable_Ioi_abs.mono_set (by
    intro y hy
    simpa [Set.mem_Ioi] using (lt_trans (by norm_num : (0 : Real) < (1 : Real)) hy))

/- `e^{1/2} + 1 < 11/4`. -/
lemma bump_ehalf_add_one_lt_quarter : Real.exp (1 / 2 : Real) + 1 < (11 / 4 : Real) := by
  have he := ConnesWeilRH.Source.Dev.Wall14Coeff.expHalf_lt
  linarith


/- Near integral on (0,1] is <= 11/4. -/
lemma bump_near_integral_le :
    (∫ y in Ioc (0 : Real) 1, |bumpArchG y|) <= (11 / 4 : Real) := by
  let mu : Measure Real := volume.restrict (Ioc (0 : Real) 1)
  let K : Real := Real.exp (1 / 2 : Real) + 1
  have hmeas : MeasurableSet (Ioc (0 : Real) 1) := measurableSet_Ioc
  have hbnd : (fun y : Real => |bumpArchG y|) ≤ᵐ[mu] (fun _ : Real => K) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict hmeas] with y hy
    exact bumpG_abs_le_near y (le_of_lt hy.1) (by simpa using hy.2)
  have hnon : (fun _ : Real => (0 : Real)) ≤ᵐ[mu] (fun y : Real => |bumpArchG y|) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict hmeas] with y hy
    exact abs_nonneg (bumpArchG y)
  have hfin : (volume : Measure Real) (Ioc (0 : Real) 1) ≠ ⊤ := by
    simp [Real.volume_Ioc]
  haveI : IsFiniteMeasure mu := MeasureTheory.isFiniteMeasure_restrict.mpr
    (by simpa [mu] using hfin)
  have hKint : Integrable (fun _ : Real => K) mu := MeasureTheory.integrable_const K
  have hsum_eq : (∫ y : Real, K ∂mu) = K := by
    calc
      (∫ y : Real, K ∂mu) = mu.real Set.univ * K := by simp [MeasureTheory.integral_const]
      _ = K := by
        have hvol : mu Set.univ = (1 : ENNReal) := by simp [mu, Real.volume_Ioc]
        have hreal : mu.real Set.univ = 1 := by
          change (mu Set.univ).toReal = (1 : Real)
          rw [hvol]
          simp
        rw [hreal]
        norm_num
  have hmm : (∫ y : Real, |bumpArchG y| ∂mu) <= (∫ y : Real, K ∂mu) :=
    MeasureTheory.integral_mono_of_nonneg hnon hKint hbnd
  calc
    (∫ y in Ioc (0 : Real) 1, |bumpArchG y|) <= (∫ y : Real, K ∂mu) := by
      simpa [mu] using hmm
    _ = K := hsum_eq
    _ <= (11 / 4 : Real) := by nlinarith [ConnesWeilRH.Source.Dev.Wall14Coeff.expHalf_lt]




lemma bump_tail_const_le : (2 * Real.exp (-1 : Real)) / (1 - Real.exp (-2 : Real)) <= (4 / 3 : Real) := by
  let tum : Real := Real.exp (-1 : Real)
  have hle_t : tum <= (1 / 2 : Real) := by
    have he : (2 : Real) <= Real.exp 1 := by
      rw [show (2 : Real) = (1 : Real) + 1 by norm_num]
      exact Real.add_one_le_exp (1 : Real)
    have hpos : (0 : Real) < Real.exp 1 := Real.exp_pos (1 : Real)
    have hstep : (1 / Real.exp 1 : Real) <= (1 / 2 : Real) := by
      rw [div_le_iff₀ hpos]
      nlinarith [he]
    unfold tum
    rw [Real.exp_neg]
    simpa [one_div] using hstep
  have hsq : tum^2 = Real.exp (-2 : Real) := by
    unfold tum
    rw [pow_two, ← Real.exp_add]
    norm_num
  have hden : (0 : Real) < 1 - tum^2 := by
    have ht0 : 0 < tum := by
      unfold tum
      exact Real.exp_pos (-1 : Real)
    have hlt : tum < (1 : Real) := by nlinarith [hle_t]
    nlinarith [ht0, hlt]
  have hhi : 2 * tum / (1 - tum^2) <= (4 / 3 : Real) := by
    rw [div_le_iff₀ hden]
    nlinarith
  calc
    (2 * Real.exp (-1 : Real)) / (1 - Real.exp (-2 : Real))
        = 2 * tum / (1 - tum^2) := by simp [tum, hsq]
    _ <= (4 / 3 : Real) := hhi



/- Tail integral, mirroring PlateauIntegrateH.int_tail_gate_le. -/
lemma bump_tail_feas :
    (∫ y in Ioi (1 : Real) , |bumpArchG y|) <= (2 * bumpA) * (Real.exp (-1 : Real) / (1 - Real.exp (-2 : Real))) := by
  let mu : Measure ℝ := volume.restrict (Ioi (1 : ℝ))
  let cden : ℝ := 1 - Real.exp (-2 : ℝ)
  have hcden : 0 < cden := by
    unfold cden
    have helt : Real.exp (-2 : ℝ) < (1 : ℝ) :=
      by simpa using (Real.exp_lt_exp.mpr (by norm_num : (-2 : ℝ) < (0 : ℝ)))
    nlinarith
  have hden_ne : cden ≠ 0 := ne_of_gt hcden
  have hmeas : MeasurableSet (Ioi (1 : ℝ)) := isOpen_Ioi.measurableSet
  have bnd : (fun y : ℝ => |bumpArchG y|) ≤ᵐ[mu]
      (fun y : ℝ => (2 * bumpA) * (Real.exp (-y) / cden)) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict hmeas] with y hy
    exact bump_whole_exp y (by exact le_of_lt hy)
  have hnon : (fun _ : ℝ => (0 : ℝ)) ≤ᵐ[mu] (fun y : ℝ => |bumpArchG y|) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict hmeas] with y hy
    exact abs_nonneg (bumpArchG y)
  have hexp : Integrable (fun y : ℝ => Real.exp (-y)) mu := by
    change Integrable (fun y : ℝ => Real.exp (-y)) (volume.restrict (Ioi (1 : ℝ)))
    exact integrableOn_exp_neg_Ioi (1 : ℝ)
  have hbint : Integrable (fun y : ℝ => (2 * bumpA) * (Real.exp (-y) / cden)) mu := by
    have coax : (fun y : ℝ => (2 * bumpA) * (Real.exp (-y) / cden)) =
        (fun y : ℝ => ((2 * bumpA) / cden) * Real.exp (-y)) := by
      funext y
      field_simp [hden_ne, Real.exp_ne_zero, cden]
    rw [coax]
    exact hexp.const_mul (((2 * bumpA) / cden))
  have him := MeasureTheory.integral_mono_of_nonneg (μ := mu) hnon hbint bnd
  have hright : (∫ y : ℝ, (2 * bumpA) * (Real.exp (-y) / cden) ∂mu)
      = (2 * bumpA) * (Real.exp (-1) / cden) := by
    calc
      (∫ y : ℝ, (2 * bumpA) * (Real.exp (-y) / cden) ∂mu) =
          (∫ y : ℝ, ((2 * bumpA) / cden) * Real.exp (-y) ∂mu) := by
        congr 1
        funext y
        field_simp [hden_ne, Real.exp_ne_zero]
      _ = ((2 * bumpA) / cden) * (∫ y : ℝ, Real.exp (-y) ∂mu) := by
        rw [MeasureTheory.integral_const_mul]
      _ = ((2 * bumpA) / cden) * Real.exp (-1) := by
        rw [integral_exp_neg_Ioi (1 : ℝ)]
      _ = (2 * bumpA) * (Real.exp (-1) / cden) := by
        field_simp [hden_ne]
  have hfin : (∫ y in Ioi (1 : ℝ), |bumpArchG y|) <= (2 * bumpA) * (Real.exp (-1) / (1 - Real.exp (-2))) := by
    calc
      (∫ y in Ioi (1 : ℝ), |bumpArchG y|) <= (∫ y : ℝ, (2 * bumpA) * (Real.exp (-y) / cden) ∂mu) := by
        simpa [mu] using him
      _ = (2 * bumpA) * (Real.exp (-1) / cden) := hright
      _ = (2 * bumpA) * (Real.exp (-1) / (1 - Real.exp (-2))) := by
        simp [cden]
  exact hfin



/- (4/3)A form of the tail bound. -/
theorem bump_tail_integral_le :
    (∫ y in Ioi (1 : ℝ), |bumpArchG y|) <= (4 / 3 : ℝ) * bumpA := by
  have hf := bump_tail_feas
  have hden : (0 : ℝ) < 1 - Real.exp (-2 : ℝ) := by
    have helt : Real.exp (-2 : ℝ) < (1 : ℝ) :=
      by simpa using (Real.exp_lt_exp.mpr (by norm_num : (-2 : ℝ) < (0 : ℝ)))
    linarith
  have hden_ne : (1 - Real.exp (-2 : ℝ)) ≠ 0 := ne_of_gt hden
  have hCf : (2 * Real.exp (-1 : ℝ)) / (1 - Real.exp (-2 : ℝ)) <= (4/3 : ℝ) := bump_tail_const_le
  calc
    (∫ y in Ioi (1 : ℝ), |bumpArchG y|)
        <= (2 * bumpA) * (Real.exp (-1 : ℝ) / (1 - Real.exp (-2 : ℝ))) := hf
    _ = bumpA * ((2 * Real.exp (-1 : ℝ)) / (1 - Real.exp (-2 : ℝ))) := by
        field_simp [hden_ne]
    _ <= bumpA * (4/3 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hCf (le_of_lt bumpA_pos)
    _ = (4 / 3 : ℝ) * bumpA := by ring





/- Split (0,inf) = (0,1] + (1,inf). -/
lemma bump_integral_split :
    (∫ y in Ioi (0 : ℝ), |bumpArchG y|)
      = (∫ y in Ioc (0 : ℝ) 1, |bumpArchG y|) + (∫ y in Ioi (1 : ℝ), |bumpArchG y|) := by
  let f : ℝ → ℝ := fun y : ℝ => |bumpArchG y|
  have r1 : IntegrableOn f (Ioc (0 : ℝ) 1) := by simpa [f] using bump_integrableOn_Ioc01_abs
  have r2 : IntegrableOn f (Ioi (1 : ℝ)) := by simpa [f] using bump_integrableOn_Ioi1_abs
  have hst : Disjoint (Ioc (0 : ℝ) 1) (Ioi (1 : ℝ)) := by
    rw [Set.disjoint_left]
    intro y hy hy2
    exact (not_lt_of_ge hy.2) hy2
  have ht : MeasurableSet (Ioi (1 : ℝ)) := isOpen_Ioi.measurableSet
  have huni : Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) = Ioi (0 : ℝ) := by
    ext y
    rw [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi, Set.mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact lt_trans (by norm_num : (0 : ℝ) < 1) h
    · intro h0
      by_cases h2 : y <= (1 : ℝ)
      · left
        exact ⟨h0, h2⟩
      · right
        exact lt_of_not_ge h2
  calc
    (∫ y in Ioi (0 : ℝ), f y) = (∫ y in (Ioc (0:ℝ) 1 ∪ Ioi (1:ℝ)), f y) := by rw [← huni]
    _ = (∫ y in Ioc (0:ℝ) 1, f y) + (∫ y in Ioi (1:ℝ), f y) :=
        MeasureTheory.setIntegral_union hst ht r1 r2



/- Sum bound: `int(0,inf) <= 11/4 + (4/3)A`. -/
lemma bump_all_integral_le :
    (∫ y in Ioi (0 : ℝ), |bumpArchG y|) <= (11 / 4 : ℝ) + (4 / 3 : ℝ) * bumpA := by
  have hn := bump_near_integral_le
  have ht := bump_tail_integral_le
  calc
    (∫ y in Ioi (0 : ℝ), |bumpArchG y|) = (∫ y in Ioc (0:ℝ) 1, |bumpArchG y|) + (∫ y in Ioi (1:ℝ), |bumpArchG y|) := bump_integral_split
    _ <= (11 / 4 : ℝ) + (4 / 3 : ℝ) * bumpA := by nlinarith [hn, ht]



/-| hI bound: strict `< (log(4pi)+gamma)*bumpA`. -/
theorem bump_hI :
    |(∫ y in (Ioi (0 : ℝ)), bumpPlateauOwner.archimedeanIntegrand y).re|
      < (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant) * bumpA := by
  have h0 : |(∫ y in Ioi (0:ℝ), bumpPlateauOwner.archimedeanIntegrand y).re|
         <= (∫ y in Ioi (0:ℝ), |bumpArchG y|) := bump_abs_re_int_Ioi_le
  have hmax : (∫ y in Ioi (0:ℝ), |bumpArchG y|) <= (11/4:ℝ) + (4/3 :ℝ) * bumpA := bump_all_integral_le
  have h11 : (11/4:ℝ) + (4/3:ℝ)*bumpA < (29/10:ℝ)*bumpA := by
    have hA : (9/5 : ℝ) <= bumpA := bumpA_ge_nine_fifths
    nlinarith
  have h22 : (29/10:ℝ)*bumpA < (Real.log (4*Real.pi) + Real.eulerMascheroniConstant) * bumpA := by
    have hcc := ConnesWeilRH.Source.Dev.Wall14Coeff.archCoeff_gt
    have hApos : 0 < bumpA := bumpA_pos
    nlinarith [hcc]
  calc
    |(∫ y in Ioi (0:ℝ), bumpPlateauOwner.archimedeanIntegrand y).re|
        <= (∫ y in Ioi (0:ℝ), |bumpArchG y|) := h0
    _ <= (11/4:ℝ) + (4/3:ℝ)*bumpA := hmax
    _ < (29/10:ℝ)*bumpA := h11
    _ < (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant) * bumpA := h22



/-- The archimedean term of the explicit bump is nonzero, closing the hI gate. -/
theorem bumpArchimedeanTerm_ne_zero : bumpPlateauOwner.archimedeanTerm ≠ 0 := by
  apply ConnesWeilRH.Source.CCM25Concrete.archimedeanTerm_ne_zero_of_lead_pos_and_integral_bound
  · exact bumpA_pos
  · simpa [bumpA] using bump_hI



/-- The strict real part: the archimedean term of the explicit bump has
positive real part (the lead piece `C * bumpA > 0` dominates the real part of the
archimedean integral `J`, `|J| < C * bumpA`).  This is the real-part closure the
healthy/compact-log archimedean bridge needs (`compactLogArchimedeanTerm` takes the
real part).  RH NOT claimed. -/
theorem bumpArchimedeanTerm_re_pos : 0 < (bumpPlateauOwner.archimedeanTerm).re := by
  rw [ConnesWeilRH.Source.CCM25Concrete.archimedeanTerm_re_eq_lead_add_integral]
  let C : ℝ := Real.log (4 * Real.pi) + Real.eulerMascheroniConstant
  let A : ℝ := bumpA
  let J : ℝ := (∫ y in Ioi (0 : ℝ), bumpPlateauOwner.archimedeanIntegrand y).re
  have hC : 0 < C := ConnesWeilRH.Source.CCM25Concrete.archimedeanCoefficient_pos
  have htest : (bumpPlateauOwner.convolutionSquare.test 0).re = A := by
    simp [A, bumpA]
  have hA : 0 < A := by simpa [A, bumpA] using bumpA_pos
  have hJ : |J| < C * A := by
    simpa [A, J, bumpA] using bump_hI
  have hlos : -(C * A) < J := by simpa using (abs_lt.mp hJ).1
  nlinarith


end Wall14Plateau
end Dev
end Source
end ConnesWeilRH
