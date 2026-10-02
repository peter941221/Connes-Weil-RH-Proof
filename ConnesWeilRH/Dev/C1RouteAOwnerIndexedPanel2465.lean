import ConnesWeilRH.Dev.C1RouteAOwnerIndexedPanel2464

/-  2465: indexed owner-panel theorem for a panel crossing zero.

On a cross-zero panel the bump maximum is the value at zero, namely
exp(-30), independently of the owner radius.  This is the final geometric
case for the indexed panel envelope; node sums and quadrature remain open. -/

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false
set_option maxRecDepth 32768

noncomputable def ownerBumpBoxCross_2465 (radius : ℝ) : ComplexRect2427 :=
  { reLo := 0, reHi := Real.exp (-30), imLo := 0, imHi := 0 }

theorem ownerRadPos_2465 (i : Fin 30) : 0 < ownerRad_2463 i := by
  fin_cases i
  · norm_num [ownerRad_2463, rad0_2460]
  · norm_num [ownerRad_2463, rad1_2460]
  · norm_num [ownerRad_2463, rad2_2460]
  · norm_num [ownerRad_2463, rad3_2460]
  · norm_num [ownerRad_2463, rad4_2460]
  · norm_num [ownerRad_2463, rad5_2460]
  · norm_num [ownerRad_2463, rad6_2460]
  · norm_num [ownerRad_2463, rad7_2460]
  · norm_num [ownerRad_2463, rad8_2460]
  · norm_num [ownerRad_2463, rad9_2460]
  · norm_num [ownerRad_2463, rad10_2460]
  · norm_num [ownerRad_2463, rad11_2460]
  · norm_num [ownerRad_2463, rad12_2460]
  · norm_num [ownerRad_2463, rad13_2460]
  · norm_num [ownerRad_2463, rad14_2460]
  · norm_num [ownerRad_2463, rad15_2460]
  · norm_num [ownerRad_2463, rad16_2460]
  · norm_num [ownerRad_2463, rad17_2460]
  · norm_num [ownerRad_2463, rad18_2460]
  · norm_num [ownerRad_2463, rad19_2460]
  · norm_num [ownerRad_2463, rad20_2460]
  · norm_num [ownerRad_2463, rad21_2460]
  · norm_num [ownerRad_2463, rad22_2460]
  · norm_num [ownerRad_2463, rad23_2460]
  · norm_num [ownerRad_2463, rad24_2460]
  · norm_num [ownerRad_2463, rad25_2460]
  · norm_num [ownerRad_2463, rad26_2460]
  · norm_num [ownerRad_2463, rad27_2460]
  · norm_num [ownerRad_2463, rad28_2460]
  · norm_num [ownerRad_2463, rad29_2460]

theorem ownerBumpMemCross_2465 {radius x : ℝ} (hradius : 0 < radius) :
    (ownerBumpBoxCross_2465 radius).Mem
      (C1RouteAOwnerScaleAudit.widthBump radius x : ℂ) := by
  by_cases hin : |x| < radius
  · have hq : 0 < 1 - (x / radius) ^ 2 := by
      have habs : |x / radius| < 1 := by
        rw [abs_div, abs_of_pos hradius]
        apply (div_lt_iff₀ hradius).2
        simpa using hin
      have hb := abs_lt.mp habs
      nlinarith
    have hqle : 1 - (x / radius) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (x / radius)]
    have hexp : Real.exp ((-(30 : ℝ)) / (1 - (x / radius) ^ 2)) ≤
        Real.exp (-30) := by
      apply Real.exp_le_exp.mpr
      apply (div_le_iff₀ hq).2
      nlinarith
    have hnonneg : 0 ≤ Real.exp ((-(30 : ℝ)) /
        (1 - (x / radius) ^ 2)) := le_of_lt (Real.exp_pos _)
    refine ⟨?_, ?_, le_refl 0, le_refl 0⟩
    · change 0 ≤ C1RouteAOwnerScaleAudit.widthBump radius x
      simpa [C1RouteAOwnerScaleAudit.widthBump, hin] using hnonneg
    · change C1RouteAOwnerScaleAudit.widthBump radius x ≤ Real.exp (-30)
      simpa [C1RouteAOwnerScaleAudit.widthBump, hin] using hexp
  · have hz : C1RouteAOwnerScaleAudit.widthBump radius x = 0 := by
      simp [C1RouteAOwnerScaleAudit.widthBump, hin]
    refine ⟨?_, ?_, le_refl 0, le_refl 0⟩
    · simpa [ownerBumpBoxCross_2465, hz, Complex.ofReal_re]
    · have hpos : 0 ≤ Real.exp (-30) := le_of_lt (Real.exp_pos _)
      simpa [ownerBumpBoxCross_2465, hz, Complex.ofReal_re] using hpos

noncomputable def ownerPanelRectCross_2465 (x0 x1 : ℝ) (i : Fin 30) :
    ComplexRect2427 :=
  ComplexRect2427.mul
    (ComplexRect2427.mul (ownerCoefRect_2463 i)
      (ownerBumpBoxCross_2465 (ownerRad_2463 i)))
    (ownerPhaseBox_2463 (ownerMod_2463 i) x0 x1)

theorem ownerFamilyPanelMemCross_2465 {x0 x1 : ℝ}
    (h01 : x0 ≤ x1) (hx0 : x0 ≤ 0) (hx1 : 0 ≤ x1) (i : Fin 30)
    (x : ℝ) (hx : x ∈ Set.Icc x0 x1) :
    (ownerPanelRectCross_2465 x0 x1 i).Mem
      (externalFamilyValue2344 (ownerCoef_2463 i) (ownerMod_2463 i)
        (ownerRad_2463 i) x) := by
  rw [externalFamilyValue2344_eq_familyTerm]
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.mem_mul (ownerCoefMem_2463 i)
      (ownerBumpMemCross_2465 (ownerRadPos_2465 i) ))
    (ownerPhaseMem_2463 h01 hx)

theorem ownerPanelMemCross_2465 {x0 x1 : ℝ}
    (h01 : x0 ≤ x1) (hx0 : x0 ≤ 0) (hx1 : 0 ≤ x1) (x : ℝ)
    (hx : x ∈ Set.Icc x0 x1) :
    (ComplexRect2427.sumFinset (ownerPanelRectCross_2465 x0 x1) Finset.univ).Mem
      (∑ i : Fin 30,
        externalFamilyValue2344 (ownerCoef_2463 i) (ownerMod_2463 i)
          (ownerRad_2463 i) x) := by
  exact sumPanelMem_2459 (ownerPanelRectCross_2465 x0 x1)
    (fun i x hx => ownerFamilyPanelMemCross_2465 h01 hx0 hx1 i x hx) x hx

end ConnesWeilRH.Dev
