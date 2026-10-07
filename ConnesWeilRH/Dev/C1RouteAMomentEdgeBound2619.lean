import ConnesWeilRH.Dev.C1RouteAMomentResidualStability2619

namespace ConnesWeilRH.Dev

open Set

noncomputable def momentEdgeUpper2619 (radius nodeReal cut : ℝ) : ℝ :=
  Real.exp (-30 / (1 - cut ^ 2) + |nodeReal * radius|)

theorem realNormalizedMomentIntegrand2618_nonneg (radius nodeReal position : ℝ) :
    0 ≤ realNormalizedMomentIntegrand2618 radius nodeReal position := by
  unfold realNormalizedMomentIntegrand2618
  split_ifs <;> positivity

theorem realNormalizedMomentIntegrand2618_le_edgeUpper
    (radius nodeReal cut position : ℝ) (hcutNonneg : 0 ≤ cut) (hcut : cut < 1)
    (hposition : cut ≤ |position|) :
    realNormalizedMomentIntegrand2618 radius nodeReal position ≤
      momentEdgeUpper2619 radius nodeReal cut := by
  by_cases hinside : |position| < 1
  · have hdeficit : 0 < 1 - position ^ 2 := by
      have hsmall := (sq_lt_one_iff_abs_lt_one position).mpr hinside
      linarith
    have hcutDeficit : 0 < 1 - cut ^ 2 := by nlinarith
    have hdenominator : 1 - position ^ 2 ≤ 1 - cut ^ 2 := by
      nlinarith [sq_abs position, abs_nonneg position]
    have hquotient : (30 : ℝ) / (1 - cut ^ 2) ≤ 30 / (1 - position ^ 2) :=
      div_le_div_of_nonneg_left (by norm_num) hdeficit hdenominator
    have hlinear : nodeReal * radius * position ≤ |nodeReal * radius| := by
      calc
        _ ≤ |nodeReal * radius * position| := le_abs_self _
        _ = |nodeReal * radius| * |position| := abs_mul _ _
        _ ≤ |nodeReal * radius| * 1 :=
          mul_le_mul_of_nonneg_left hinside.le (abs_nonneg _)
        _ = _ := mul_one _
    simp only [realNormalizedMomentIntegrand2618, if_pos hinside, momentEdgeUpper2619]
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div]
    linarith
  · simp only [realNormalizedMomentIntegrand2618, if_neg hinside]
    exact (Real.exp_pos _).le

theorem realNormalizedMomentIntegrand2618_edge_integral_bound
    (radius nodeReal cut : ℝ) (hcutNonneg : 0 ≤ cut) (hcut : cut < 1) :
    |(∫ position in (-1 : ℝ)..(-cut), realNormalizedMomentIntegrand2618 radius nodeReal position) +
      (∫ position in cut..1, realNormalizedMomentIntegrand2618 radius nodeReal position)| ≤
      2 * (1 - cut) * momentEdgeUpper2619 radius nodeReal cut := by
  have hleftOrder : (-1 : ℝ) ≤ -cut := by linarith
  have hrightOrder : cut ≤ 1 := hcut.le
  have hleft := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1 : ℝ)) (b := -cut)
    (f := realNormalizedMomentIntegrand2618 radius nodeReal)
    (C := momentEdgeUpper2619 radius nodeReal cut) (by
      intro position hposition
      rw [Set.uIoc_of_le hleftOrder] at hposition
      rw [Real.norm_eq_abs, abs_of_nonneg (realNormalizedMomentIntegrand2618_nonneg _ _ _)]
      apply realNormalizedMomentIntegrand2618_le_edgeUpper radius nodeReal cut position hcutNonneg hcut
      linarith [hposition.2, neg_le_abs position])
  have hright := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := cut) (b := (1 : ℝ))
    (f := realNormalizedMomentIntegrand2618 radius nodeReal)
    (C := momentEdgeUpper2619 radius nodeReal cut) (by
      intro position hposition
      rw [Set.uIoc_of_le hrightOrder] at hposition
      rw [Real.norm_eq_abs, abs_of_nonneg (realNormalizedMomentIntegrand2618_nonneg _ _ _)]
      exact realNormalizedMomentIntegrand2618_le_edgeUpper radius nodeReal cut position
        hcutNonneg hcut (hposition.1.le.trans (le_abs_self position)))
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ -cut - (-1 : ℝ))] at hleft
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 - cut)] at hright
  have htriangle := norm_add_le
    (∫ position in (-1 : ℝ)..(-cut), realNormalizedMomentIntegrand2618 radius nodeReal position)
    (∫ position in cut..1, realNormalizedMomentIntegrand2618 radius nodeReal position)
  simp only [Real.norm_eq_abs] at htriangle
  nlinarith

end ConnesWeilRH.Dev
