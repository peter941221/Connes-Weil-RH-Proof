import ConnesWeilRH.Dev.C1RouteAWeightedTaxiBallBridge3241

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2680Cell16923BumpInterval3242
    (family : Fin 30) : RealInterval2429 :=
  let x : ℝ := |record2680Center3212 16923|
  let radius : ℝ := storedWidth family ^ 2
  let baseS : ℝ := ∑ m ∈ Finset.range 30, (-1 / 2 : ℝ) ^ m / (m.factorial : ℝ)
  let baseE : ℝ := |(-1 / 2 : ℝ)| ^ 30 *
    ((30 : ℕ).succ / ((30 : ℕ).factorial * 30))
  let baseLower : ℝ := baseS - baseE
  let baseUpper : ℝ := baseS + baseE
  let tAdd : ℝ := 30 - 30 / (1 - (x / radius) ^ 2)
  let scaledS : ℝ := ∑ m ∈ Finset.range 30,
    (tAdd / 8) ^ m / (m.factorial : ℝ)
  let scaledE : ℝ := |tAdd / 8| ^ 30 *
    ((30 : ℕ).succ / ((30 : ℕ).factorial * 30))
  let addendLower : ℝ := (scaledS - scaledE) ^ 8
  { lo := baseLower ^ 60 * addendLower
    hi := baseUpper ^ 60 * (scaledS + scaledE) ^ 8 }

theorem record2680_cell16923_center_neg3242 :
    record2680Center3212 16923 < 0 := by
  norm_num [record2680Center3212, record2680Grid3212,
    diagnosticRadius3201]

set_option maxHeartbeats 10000000 in
theorem record2680_cell16923_bump_mem3242 {family : Fin 30} :
    (record2680Cell16923BumpInterval3242 family).Mem
      (widthBump (storedWidth family ^ 2) (record2680Center3212 16923)) := by
  let x : ℝ := |record2680Center3212 16923|
  let radius : ℝ := storedWidth family ^ 2
  let baseS : ℝ := ∑ m ∈ Finset.range 30, (-1 / 2 : ℝ) ^ m / (m.factorial : ℝ)
  let baseE : ℝ := |(-1 / 2 : ℝ)| ^ 30 *
    ((30 : ℕ).succ / ((30 : ℕ).factorial * 30))
  let baseLower : ℝ := baseS - baseE
  let baseUpper : ℝ := baseS + baseE
  let tAdd : ℝ := 30 - 30 / (1 - (x / radius) ^ 2)
  let scaledS : ℝ := ∑ m ∈ Finset.range 30,
    (tAdd / 8) ^ m / (m.factorial : ℝ)
  let scaledE : ℝ := |tAdd / 8| ^ 30 *
    ((30 : ℕ).succ / ((30 : ℕ).factorial * 30))
  let addendLower : ℝ := (scaledS - scaledE) ^ 8
  have hxneg : record2680Center3212 16923 < 0 :=
    record2680_cell16923_center_neg3242
  have hx : 0 ≤ x := by
    exact abs_nonneg _
  have hcenter_abs : x = -record2680Center3212 16923 := by
    dsimp [x]
    rw [abs_of_neg hxneg]
  have hTaylor := expTwoSided2676 (n := 30) (by norm_num)
      (by norm_num : |(-1 / 2 : ℝ)| ≤ 1)
      (S := baseS) (E := baseE) rfl rfl
  have hbaseLowerNonneg : 0 ≤ baseLower := by
    dsimp [baseLower, baseS, baseE]
    norm_num
  have hbase : baseLower ^ 60 ≤ Real.exp (-30 : ℝ) ∧
      Real.exp (-30 : ℝ) ≤ baseUpper ^ 60 := by
    have hexp60 : Real.exp (-1 / 2 : ℝ) ^ 60 = Real.exp (-30 : ℝ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
    constructor
    · calc
        baseLower ^ 60 ≤ Real.exp (-1 / 2 : ℝ) ^ 60 :=
          pow_le_pow_left₀ hbaseLowerNonneg hTaylor.1 60
        _ = Real.exp (-30 : ℝ) := hexp60
    · calc
        Real.exp (-30 : ℝ) = Real.exp (-1 / 2 : ℝ) ^ 60 := hexp60.symm
        _ ≤ baseUpper ^ 60 :=
          pow_le_pow_left₀ (Real.exp_pos _).le hTaylor.2 60
  have hloBase : baseLower ^ 60 ≤ Real.exp (-30 : ℝ) := hbase.1
  have hhiPin : Real.exp (-30 : ℝ) ≤ baseUpper ^ 60 := hbase.2
  have ht0 : tAdd ≤ 0 := by
    dsimp [tAdd, x, radius]
    fin_cases family <;>
      norm_num [storedWidth, Matrix.cons_val_zero, Matrix.cons_val_four,
        record2680Center3212, record2680Grid3212, diagnosticRadius3201,
        Fin.ext_iff]
  have ht1 : -8 ≤ tAdd := by
    dsimp [tAdd, x, radius]
    fin_cases family <;>
      norm_num [storedWidth, Matrix.cons_val_zero, Matrix.cons_val_four,
        record2680Center3212, record2680Grid3212, diagnosticRadius3201,
        Fin.ext_iff]
  have hscaled0 : -(1 : ℝ) ≤ tAdd / 8 := by linarith
  have hscaled1 : tAdd / 8 ≤ 0 := by linarith
  have hscaled_abs : |tAdd / 8| ≤ 1 := by
    exact abs_le.mpr ⟨hscaled0, hscaled1.trans (by norm_num)⟩
  have hscaled := expTwoSided2676 (n := 30) (by norm_num)
    hscaled_abs (S := scaledS) (E := scaledE) rfl rfl
  have hscaled_nonneg : 0 ≤ scaledS - scaledE := by
    dsimp [scaledS, scaledE]
    fin_cases family <;>
      norm_num [tAdd, x, radius, storedWidth, Matrix.cons_val_zero,
        Matrix.cons_val_four, record2680Center3212, record2680Grid3212,
        diagnosticRadius3201, Fin.ext_iff]
  have hadd : (scaledS - scaledE) ^ 8 ≤ Real.exp tAdd := by
    calc
      (scaledS - scaledE) ^ 8 ≤ Real.exp (tAdd / 8) ^ 8 :=
        pow_le_pow_left₀ hscaled_nonneg hscaled.1 8
      _ = Real.exp tAdd := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hpLo : addendLower ≤ Real.exp
      (30 - 30 / (1 - (x / radius) ^ 2)) := by
    simpa [addendLower, tAdd] using hadd
  have hXr : x < radius := by
    have hx2 : x < 2 := by
      dsimp [x]
      norm_num [record2680Center3212, record2680Grid3212,
        diagnosticRadius3201]
    have hr2 : 2 ≤ radius := by
      dsimp [radius]
      fin_cases family <;>
        norm_num [storedWidth, Matrix.cons_val_zero, Matrix.cons_val_four,
          Fin.ext_iff]
    linarith
  have hbox := bumpBoxMem2676
    (x := x) (X := x) (radius := radius)
    (loBase := baseLower ^ 60) (pLo := addendLower)
    (hiPin := baseUpper ^ 60) hx (le_rfl) hXr hloBase hhiPin hpLo
    (by positivity)
  have hcenter : record2680Center3212 16923 = -x := by
    linarith [hcenter_abs]
  rw [hcenter]
  have hscaled_upper : Real.exp (tAdd / 8) ^ 8 ≤
      (scaledS + scaledE) ^ 8 := by
    exact pow_le_pow_left₀ (Real.exp_pos _).le hscaled.2 8
  have hupper_exp : Real.exp tAdd ≤ (scaledS + scaledE) ^ 8 := by
    calc
      Real.exp tAdd = Real.exp (tAdd / 8) ^ 8 := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ (scaledS + scaledE) ^ 8 := hscaled_upper
  have hwidth_x : widthBump radius x =
      Real.exp (-30 : ℝ) * Real.exp tAdd := by
    rw [widthBump]
    have hinside : |x| < radius := by
      rw [abs_of_nonneg hx]
      exact hXr
    rw [if_pos hinside]
    rw [← Real.exp_add]
    congr 1
    dsimp [tAdd]
    field_simp
    ring
  have hupper_x : widthBump radius x ≤
      baseUpper ^ 60 * (scaledS + scaledE) ^ 8 := by
    rw [hwidth_x]
    calc
      Real.exp (-30 : ℝ) * Real.exp tAdd ≤
          baseUpper ^ 60 * Real.exp tAdd :=
        mul_le_mul_of_nonneg_right hbase.2 (Real.exp_nonneg _)
      _ ≤ baseUpper ^ 60 * (scaledS + scaledE) ^ 8 :=
        mul_le_mul_of_nonneg_left hupper_exp (by positivity)
  have hwidth : widthBump radius (-x) = widthBump radius x := by
    simp [widthBump, abs_of_nonneg hx]
    ring_nf
  rw [hwidth]
  simpa [record2680Cell16923BumpInterval3242, x, radius,
    baseS, baseE, baseLower, baseUpper, tAdd, scaledS, scaledE,
    addendLower] using ⟨hbox.1, hupper_x⟩

end ConnesWeilRH.Dev
