import ConnesWeilRH.Dev.C1RouteAOwnerIndexedPanel2463

/-  2464: indexed owner-panel theorem on the nonpositive half-line.

The endpoint x1 is the bump maximum on the left half-line.  This is the
left-sided companion of 2463; cross-zero panels remain a separate case.  -/

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false
set_option maxRecDepth 32768

noncomputable def ownerBumpBoxLeft_2464 (radius x1 : ℝ) : ComplexRect2427 :=
  { reLo := 0,
    reHi := if -radius < x1 then
      Real.exp ((-(30 : ℝ)) / (1 - (x1 / radius) ^ 2)) else 0,
    imLo := 0, imHi := 0 }

noncomputable def ownerPanelRectLeft_2464 (x0 x1 : ℝ) (i : Fin 30) :
    ComplexRect2427 :=
  ComplexRect2427.mul
    (ComplexRect2427.mul (ownerCoefRect_2463 i)
      (ownerBumpBoxLeft_2464 (ownerRad_2463 i) x1))
    (ownerPhaseBox_2463 (ownerMod_2463 i) x0 x1)

theorem ownerBumpMemLeft_2464 {radius x0 x1 x : ℝ}
    (h01 : x0 ≤ x1) (hx1 : x1 ≤ 0) (hx : x ∈ Set.Icc x0 x1) :
    (ownerBumpBoxLeft_2464 radius x1).Mem
      (C1RouteAOwnerScaleAudit.widthBump radius x : ℂ) := by
  by_cases h1 : -radius < x1
  · have hX1in : |x1| < radius := by
      rw [abs_of_nonpos hx1]
      linarith
    have hbox : 0 ≤ Real.exp ((-(30 : ℝ)) / (1 - (x1 / radius) ^ 2)) :=
      le_of_lt (Real.exp_pos _)
    by_cases hin : |x| < radius
    · have hx0 : -radius < x := by
        have hxn : x ≤ 0 := le_trans hx.2 hx1
        rw [abs_of_nonpos hxn] at hin
        linarith
      have hsup := widthBump_mono_left_2459 radius
        ⟨hx0, le_trans hx.2 hx1⟩ ⟨h1, hx1⟩ hx.2
      have hX1b : C1RouteAOwnerScaleAudit.widthBump radius x1 =
          Real.exp ((-(30 : ℝ)) / (1 - (x1 / radius) ^ 2)) := by
        simp [C1RouteAOwnerScaleAudit.widthBump, hX1in]
      refine ⟨?_, ?_, le_refl 0, le_refl 0⟩
      · simpa [ownerBumpBoxLeft_2464, h1, Complex.ofReal_re] using
          widthBump_nonneg_2460 radius x
      · have h2 := le_trans hsup (le_of_eq hX1b)
        simpa [ownerBumpBoxLeft_2464, h1, Complex.ofReal_re] using h2
    · have hz : C1RouteAOwnerScaleAudit.widthBump radius x = 0 := by
        simp [C1RouteAOwnerScaleAudit.widthBump, hin]
      refine ⟨?_, ?_, le_refl 0, le_refl 0⟩
      · simpa [ownerBumpBoxLeft_2464, h1, Complex.ofReal_re, hz]
      · simpa [ownerBumpBoxLeft_2464, h1, Complex.ofReal_re, hz] using hbox
  · have hge : x1 ≤ -radius := le_of_not_gt h1
    have hout : ¬ |x| < radius := by
      intro hin
      have hxn : x ≤ 0 := le_trans hx.2 hx1
      rw [abs_of_nonpos hxn] at hin
      have hxr : radius ≤ -x := by linarith [hge, hx.2]
      exact (not_lt_of_ge hxr) hin
    have hz : C1RouteAOwnerScaleAudit.widthBump radius x = 0 := by
      simp [C1RouteAOwnerScaleAudit.widthBump, hout]
    refine ⟨?_, ?_, le_refl 0, le_refl 0⟩
    · simpa [ownerBumpBoxLeft_2464, h1, Complex.ofReal_re, hz]
    · simpa [ownerBumpBoxLeft_2464, h1, Complex.ofReal_re, hz]

theorem ownerFamilyPanelMemLeft_2464 {x0 x1 : ℝ}
    (h01 : x0 ≤ x1) (hx1 : x1 ≤ 0) (i : Fin 30)
    (x : ℝ) (hx : x ∈ Set.Icc x0 x1) :
    (ownerPanelRectLeft_2464 x0 x1 i).Mem
      (externalFamilyValue2344 (ownerCoef_2463 i) (ownerMod_2463 i)
        (ownerRad_2463 i) x) := by
  rw [externalFamilyValue2344_eq_familyTerm]
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.mem_mul (ownerCoefMem_2463 i)
      (ownerBumpMemLeft_2464 h01 hx1 hx))
    (ownerPhaseMem_2463 h01 hx)

theorem ownerPanelMemLeft_2464 {x0 x1 : ℝ}
    (h01 : x0 ≤ x1) (hx1 : x1 ≤ 0) (x : ℝ)
    (hx : x ∈ Set.Icc x0 x1) :
    (ComplexRect2427.sumFinset (ownerPanelRectLeft_2464 x0 x1) Finset.univ).Mem
      (∑ i : Fin 30,
        externalFamilyValue2344 (ownerCoef_2463 i) (ownerMod_2463 i)
          (ownerRad_2463 i) x) := by
  exact sumPanelMem_2459 (ownerPanelRectLeft_2464 x0 x1)
    (fun i x hx => ownerFamilyPanelMemLeft_2464 h01 hx1 i x hx) x hx

end ConnesWeilRH.Dev
