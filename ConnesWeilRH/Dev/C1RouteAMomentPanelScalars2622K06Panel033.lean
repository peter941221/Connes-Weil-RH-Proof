import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P033 : ℚ := ((-21025701 : ℚ) / 453850)

def momentPanelGrowth2622K06P033 : ℚ := ((900576001 : ℚ) / 1139400025)

theorem momentPanelPhase_owner2622K06P033 :
    (momentPanelPhase2622K06P033 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-113 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P033, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P033 :
    (momentPanelGrowth2622K06P033 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-113 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P033, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P033Input : RatPair2542 := (momentPanelPhase2622K06P033 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P033Expected : RatState2542 :=
  ((((8106331853723677147913564956851722011678982500012716983514579991917793056303 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((20555318764963281112225346079 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P033_replay :
    compactExp2620 momentScalarAmp2622K06P033Input 20 = momentScalarAmp2622K06P033Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P033_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-113 / 200) 0) -
      (momentScalarAmp2622K06P033Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P033Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P033 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P033]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P033 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P033 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P033Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P033Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P033_replay] at h
  simpa only [momentPanelPhase_owner2622K06P033] using h

theorem momentScalarAmp2622K06P033_radius_le :
    (momentScalarAmp2622K06P033Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P033Expected]

def momentScalarGrow2622K06P033Input : RatPair2542 := (momentPanelGrowth2622K06P033 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P033Expected : RatState2542 :=
  ((((4708285269182928461200281617497124717171537686295696173119378493865080509722356597988199283223051 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5968456148624820688116076670341546511435363153587 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P033_replay :
    compactExp2620 momentScalarGrow2622K06P033Input 20 = momentScalarGrow2622K06P033Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P033_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-113 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P033Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P033Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P033 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P033]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P033 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P033 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P033Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P033Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P033_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P033] using h

theorem momentScalarGrow2622K06P033_radius_le :
    (momentScalarGrow2622K06P033Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P033Expected]

end ConnesWeilRH.Dev
