import ConnesWeilRH.Dev.C1RouteAOwnerPanelSample2460

/-  2463: indexed owner-panel theorem on the nonnegative half-line.

This lifts the 2460 one-panel family proofs to arbitrary x0 <= x1 with
0 <= x0.  The bump endpoint is selected by the exact support branch at x0;
the phase box uses |modulation|, so no sign-specific panel theorem is needed.
The finite-family sum is still composed before any modulus through the 2459
sum door.  The negative half-line and the cross-zero panel are separate
geometry obligations; this file intentionally does not claim them.  -/

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false
set_option maxRecDepth 32768

def ownerCoefRect_2463 (i : Fin 30) : ComplexRect2427 :=
  match i.val with
  | 0 => coefRect0_2460 | 1 => coefRect1_2460 | 2 => coefRect2_2460
  | 3 => coefRect3_2460 | 4 => coefRect4_2460 | 5 => coefRect5_2460
  | 6 => coefRect6_2460 | 7 => coefRect7_2460 | 8 => coefRect8_2460
  | 9 => coefRect9_2460 | 10 => coefRect10_2460 | 11 => coefRect11_2460
  | 12 => coefRect12_2460 | 13 => coefRect13_2460 | 14 => coefRect14_2460
  | 15 => coefRect15_2460 | 16 => coefRect16_2460 | 17 => coefRect17_2460
  | 18 => coefRect18_2460 | 19 => coefRect19_2460 | 20 => coefRect20_2460
  | 21 => coefRect21_2460 | 22 => coefRect22_2460 | 23 => coefRect23_2460
  | 24 => coefRect24_2460 | 25 => coefRect25_2460 | 26 => coefRect26_2460
  | 27 => coefRect27_2460 | 28 => coefRect28_2460 | 29 => coefRect29_2460
  | _ => { reLo := 0, reHi := 0, imLo := 0, imHi := 0 }

def ownerCoef_2463 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => coef0_2460 | 1 => coef1_2460 | 2 => coef2_2460
  | 3 => coef3_2460 | 4 => coef4_2460 | 5 => coef5_2460
  | 6 => coef6_2460 | 7 => coef7_2460 | 8 => coef8_2460
  | 9 => coef9_2460 | 10 => coef10_2460 | 11 => coef11_2460
  | 12 => coef12_2460 | 13 => coef13_2460 | 14 => coef14_2460
  | 15 => coef15_2460 | 16 => coef16_2460 | 17 => coef17_2460
  | 18 => coef18_2460 | 19 => coef19_2460 | 20 => coef20_2460
  | 21 => coef21_2460 | 22 => coef22_2460 | 23 => coef23_2460
  | 24 => coef24_2460 | 25 => coef25_2460 | 26 => coef26_2460
  | 27 => coef27_2460 | 28 => coef28_2460 | 29 => coef29_2460
  | _ => 0

def ownerMod_2463 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => mod0_2460 | 1 => mod1_2460 | 2 => mod2_2460
  | 3 => mod3_2460 | 4 => mod4_2460 | 5 => mod5_2460
  | 6 => mod6_2460 | 7 => mod7_2460 | 8 => mod8_2460
  | 9 => mod9_2460 | 10 => mod10_2460 | 11 => mod11_2460
  | 12 => mod12_2460 | 13 => mod13_2460 | 14 => mod14_2460
  | 15 => mod15_2460 | 16 => mod16_2460 | 17 => mod17_2460
  | 18 => mod18_2460 | 19 => mod19_2460 | 20 => mod20_2460
  | 21 => mod21_2460 | 22 => mod22_2460 | 23 => mod23_2460
  | 24 => mod24_2460 | 25 => mod25_2460 | 26 => mod26_2460
  | 27 => mod27_2460 | 28 => mod28_2460 | 29 => mod29_2460
  | _ => 0

def ownerRad_2463 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => rad0_2460 | 1 => rad1_2460 | 2 => rad2_2460
  | 3 => rad3_2460 | 4 => rad4_2460 | 5 => rad5_2460
  | 6 => rad6_2460 | 7 => rad7_2460 | 8 => rad8_2460
  | 9 => rad9_2460 | 10 => rad10_2460 | 11 => rad11_2460
  | 12 => rad12_2460 | 13 => rad13_2460 | 14 => rad14_2460
  | 15 => rad15_2460 | 16 => rad16_2460 | 17 => rad17_2460
  | 18 => rad18_2460 | 19 => rad19_2460 | 20 => rad20_2460
  | 21 => rad21_2460 | 22 => rad22_2460 | 23 => rad23_2460
  | 24 => rad24_2460 | 25 => rad25_2460 | 26 => rad26_2460
  | 27 => rad27_2460 | 28 => rad28_2460 | 29 => rad29_2460
  | _ => 0

theorem ownerCoefMem_2463 (i : Fin 30) :
    (ownerCoefRect_2463 i).Mem (ownerCoef_2463 i) := by
  fin_cases i
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect0_2460, coef0_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect1_2460, coef1_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect2_2460, coef2_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect3_2460, coef3_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect4_2460, coef4_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect5_2460, coef5_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect6_2460, coef6_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect7_2460, coef7_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect8_2460, coef8_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect9_2460, coef9_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect10_2460, coef10_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect11_2460, coef11_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect12_2460, coef12_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect13_2460, coef13_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect14_2460, coef14_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect15_2460, coef15_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect16_2460, coef16_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect17_2460, coef17_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect18_2460, coef18_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect19_2460, coef19_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect20_2460, coef20_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect21_2460, coef21_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect22_2460, coef22_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect23_2460, coef23_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect24_2460, coef24_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect25_2460, coef25_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect26_2460, coef26_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect27_2460, coef27_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect28_2460, coef28_2460]
  · constructor <;> norm_num [ownerCoefRect_2463, ownerCoef_2463, coefRect29_2460, coef29_2460]

noncomputable def ownerBumpBox_2463 (radius x0 : ℝ) : ComplexRect2427 :=
  { reLo := 0,
    reHi := if x0 < radius then
      Real.exp ((-(30 : ℝ)) / (1 - (x0 / radius) ^ 2)) else 0,
    imLo := 0, imHi := 0 }

noncomputable def ownerPhaseBox_2463 (modulation x0 x1 : ℝ) : ComplexRect2427 :=
  { reLo := Real.cos (modulation * ((x0 + x1) / 2)) -
      |modulation| * (x1 - x0) / 2,
    reHi := Real.cos (modulation * ((x0 + x1) / 2)) +
      |modulation| * (x1 - x0) / 2,
    imLo := Real.sin (modulation * ((x0 + x1) / 2)) -
      |modulation| * (x1 - x0) / 2,
    imHi := Real.sin (modulation * ((x0 + x1) / 2)) +
      |modulation| * (x1 - x0) / 2 }

noncomputable def ownerPanelRect_2463 (x0 x1 : ℝ) (i : Fin 30) :
    ComplexRect2427 :=
  ComplexRect2427.mul
    (ComplexRect2427.mul (ownerCoefRect_2463 i)
      (ownerBumpBox_2463 (ownerRad_2463 i) x0))
    (ownerPhaseBox_2463 (ownerMod_2463 i) x0 x1)

theorem ownerPhaseBound_2463 {modulation x0 x1 x : ℝ}
    (h01 : x0 ≤ x1) (hx : x ∈ Set.Icc x0 x1) :
    |Real.cos (modulation * x) -
        Real.cos (modulation * ((x0 + x1) / 2))| ≤
      |modulation| * (x1 - x0) / 2 ∧
    |Real.sin (modulation * x) -
        Real.sin (modulation * ((x0 + x1) / 2))| ≤
      |modulation| * (x1 - x0) / 2 := by
  have hmid : |x - (x0 + x1) / 2| ≤ (x1 - x0) / 2 := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2]
  have harg : |modulation * x - modulation * ((x0 + x1) / 2)| ≤
      |modulation| * (x1 - x0) / 2 := by
    calc
      |modulation * x - modulation * ((x0 + x1) / 2)| =
          |modulation| * |x - (x0 + x1) / 2| := by
            have h : modulation * x - modulation * ((x0 + x1) / 2) =
                modulation * (x - (x0 + x1) / 2) := by ring
            rw [h, abs_mul]
      _ ≤ |modulation| * ((x1 - x0) / 2) := by
        exact mul_le_mul_of_nonneg_left hmid (abs_nonneg modulation)
      _ = |modulation| * (x1 - x0) / 2 := by ring
  constructor
  · exact le_trans (cos_lipschitz_2459 _ _) harg
  · exact le_trans (sin_lipschitz_2459 _ _) harg

theorem ownerBumpMem_2463 {radius x0 x1 x : ℝ}
    (h01 : x0 ≤ x1) (hx0 : 0 ≤ x0) (hx : x ∈ Set.Icc x0 x1) :
    (ownerBumpBox_2463 radius x0).Mem
      (C1RouteAOwnerScaleAudit.widthBump radius x : ℂ) := by
  by_cases h0 : x0 < radius
  · have hX0in : |x0| < radius := by
      rw [abs_of_nonneg hx0]
      exact h0
    have hbox : 0 ≤ Real.exp ((-(30 : ℝ)) / (1 - (x0 / radius) ^ 2)) :=
      le_of_lt (Real.exp_pos _)
    by_cases hin : |x| < radius
    · have hsup := widthBump_antitone_right_2459 radius
        ⟨hx0, h0⟩
          ⟨le_trans hx0 hx.1,
            by simpa [abs_of_nonneg (le_trans hx0 hx.1)] using hin⟩ hx.1
      have hX0b : C1RouteAOwnerScaleAudit.widthBump radius x0 =
          Real.exp ((-(30 : ℝ)) / (1 - (x0 / radius) ^ 2)) := by
        simp [C1RouteAOwnerScaleAudit.widthBump, hX0in]
      refine ⟨?_, ?_, le_refl 0, le_refl 0⟩
      · simpa [ownerBumpBox_2463, h0, Complex.ofReal_re] using
          widthBump_nonneg_2460 radius x
      · have h2 := le_trans hsup (le_of_eq hX0b)
        simpa [ownerBumpBox_2463, h0, Complex.ofReal_re] using h2
    · have hz : C1RouteAOwnerScaleAudit.widthBump radius x = 0 := by
        simp [C1RouteAOwnerScaleAudit.widthBump, hin]
      refine ⟨?_, ?_, le_refl 0, le_refl 0⟩
      · simpa [ownerBumpBox_2463, h0, Complex.ofReal_re, hz]
      · simpa [ownerBumpBox_2463, h0, Complex.ofReal_re, hz] using hbox
  · have hge : radius ≤ x0 := le_of_not_gt h0
    have hout : ¬ |x| < radius := by
      intro hin
      have hle : radius ≤ |x| :=
        le_trans hge (le_trans hx.1 (le_abs_self x))
      exact (not_lt_of_ge hle) hin
    have hz : C1RouteAOwnerScaleAudit.widthBump radius x = 0 := by
      simp [C1RouteAOwnerScaleAudit.widthBump, hout]
    refine ⟨?_, ?_, le_refl 0, le_refl 0⟩
    · simpa [ownerBumpBox_2463, h0, Complex.ofReal_re, hz]
    · simpa [ownerBumpBox_2463, h0, Complex.ofReal_re, hz]

theorem ownerPhaseMem_2463 {modulation x0 x1 x : ℝ}
    (h01 : x0 ≤ x1) (hx : x ∈ Set.Icc x0 x1) :
    (ownerPhaseBox_2463 modulation x0 x1).Mem
      (Complex.exp ((modulation * x : ℝ) * Complex.I) : ℂ) := by
  have hb := ownerPhaseBound_2463 (modulation := modulation) h01 hx
  have hre : (Complex.exp ((modulation * x : ℝ) * Complex.I)).re =
      Real.cos (modulation * x) := by
    rw [Complex.exp_re]
    simp
  have him : (Complex.exp ((modulation * x : ℝ) * Complex.I)).im =
      Real.sin (modulation * x) := by
    rw [Complex.exp_im]
    simp
  obtain ⟨hclo, hchi⟩ := abs_le.mp hb.1
  obtain ⟨hslo, hshi⟩ := abs_le.mp hb.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hre]; simp only [ownerPhaseBox_2463]; linarith
  · rw [hre]; simp only [ownerPhaseBox_2463]; linarith
  · rw [him]; simp only [ownerPhaseBox_2463]; linarith
  · rw [him]; simp only [ownerPhaseBox_2463]; linarith

theorem ownerFamilyPanelMem_2463 {x0 x1 : ℝ}
    (h01 : x0 ≤ x1) (hx0 : 0 ≤ x0) (i : Fin 30)
    (x : ℝ) (hx : x ∈ Set.Icc x0 x1) :
    (ownerPanelRect_2463 x0 x1 i).Mem
      (externalFamilyValue2344 (ownerCoef_2463 i) (ownerMod_2463 i)
        (ownerRad_2463 i) x) := by
  rw [externalFamilyValue2344_eq_familyTerm]
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.mem_mul (ownerCoefMem_2463 i)
      (ownerBumpMem_2463 h01 hx0 hx))
    (ownerPhaseMem_2463 h01 hx)

theorem ownerPanelMem_2463 {x0 x1 : ℝ}
    (h01 : x0 ≤ x1) (hx0 : 0 ≤ x0) (x : ℝ)
    (hx : x ∈ Set.Icc x0 x1) :
    (ComplexRect2427.sumFinset (ownerPanelRect_2463 x0 x1) Finset.univ).Mem
      (∑ i : Fin 30,
        externalFamilyValue2344 (ownerCoef_2463 i) (ownerMod_2463 i)
          (ownerRad_2463 i) x) := by
  exact sumPanelMem_2459 (ownerPanelRect_2463 x0 x1)
    (fun i x hx => ownerFamilyPanelMem_2463 h01 hx0 i x hx) x hx

end ConnesWeilRH.Dev
