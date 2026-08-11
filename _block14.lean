
/-! ### Integral assembly on (0,inf): |Re-integral| <= integral |g| -/

/-- Whole pointwise upper bound on the tail-y half line: `|g| <= 2A e^{-y}/(1-e^{-2})`. -/
lemma bump_whole_exp (y : Real) (h1 : 1 <= y) :
    |bumpArchG y| <= (2 * bumpA) * (Real.exp (-y) / (1 - Real.exp (-2 : Real))) := by
  have hA0 : 0 <= 2 * bumpA := mul_nonneg (by norm_num) (le_of_lt bumpA_pos)
  by_cases h2 : y <= 2
  . exact bumpG_abs_mid_exp y h1 h2
  . have hy2 : 2 < y := lt_of_not_ge h2
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
    . simp [archimedeanIntegrand_re_eq_bumpArchG y hy]
    . simpa using bumpPlateauOwner.archimedeanIntegrand_im_eq_zero y
  rw [heq]
  simp

/-! |Re(integral)| <= integral |g| on (0,inf). -/
lemma bump_abs_re_int_Ioi_le :
    |(∫ y in Ioi (0 : Real), bumpPlateauOwner.archimedeanIntegrand y).re|
      <= ∫ y in Ioi (0 : Real), |bumpArchG y| := by
  let mu : Measure Real := volume.restrict (Ioi (0 : Real))
  have hmeas0 : MeasurableSet (Ioi (0 : Real)) := isOpen_Ioi.measurableSet
  have hchain : |(∫ y : Real, bumpPlateauOwner.archimedeanIntegrand y mu).re|
          <= ∫ y : Real, |bumpArchG y| mu := by
    calc
      |(∫ y : Real, bumpPlateauOwner.archimedeanIntegrand y mu).re|
          <= ‖∫ y : Real, bumpPlateauOwner.archimedeanIntegrand y mu‖ := Complex.abs_re_le_norm _
      _ <= ∫ y : Real, ‖bumpPlateauOwner.archimedeanIntegrand y‖ mu :=
            MeasureTheory.norm_integral_le_integral_norm (fun y : Real => bumpPlateauOwner.archimedeanIntegrand y)
      _ = ∫ y : Real, |bumpArchG y| mu := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [MeasureTheory.self_mem_ae_restrict hmeas0] with y hy
            have hy0 : 0 < y := by simpa using hy
            exact bump_norm_integrand_eq_abs y hy0
  change |(∫ y : Real, bumpPlateauOwner.archimedeanIntegrand y mu).re| <=
            ∫ y : Real, |bumpArchG y| mu
  exact hchain