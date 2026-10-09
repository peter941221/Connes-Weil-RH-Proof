import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P008 : ℚ := ((-20729751 : ℚ) / 223850)

def momentPanelGrowth2622K06P008 : ℚ := ((25848587 : ℚ) / 5589675)

theorem momentPanelPhase_owner2622K06P008 :
    (momentPanelPhase2622K06P008 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-163 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P008, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P008 :
    (momentPanelGrowth2622K06P008 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-163 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P008, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P008Input : RatPair2542 := (momentPanelPhase2622K06P008 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P008Expected : RatState2542 :=
  ((((32319297750033796391779600570192031827799379068280936167 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2417851639229258513342755 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P008_replay :
    compactExp2620 momentScalarAmp2622K06P008Input 20 = momentScalarAmp2622K06P008Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P008_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-163 / 200) 0) -
      (momentScalarAmp2622K06P008Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P008Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P008 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P008]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P008 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P008 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P008Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P008Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P008_replay] at h
  simpa only [momentPanelPhase_owner2622K06P008] using h

theorem momentScalarAmp2622K06P008_radius_le :
    (momentScalarAmp2622K06P008Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P008Expected]

def momentScalarGrow2622K06P008Input : RatPair2542 := (momentPanelGrowth2622K06P008 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P008Expected : RatState2542 :=
  ((((217733991544767631128717844480755894289380390180021005946870377589529123723810937843768745698685431 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((69002351958678843800767832398171669528723712849979 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K06P008_replay :
    compactExp2620 momentScalarGrow2622K06P008Input 20 = momentScalarGrow2622K06P008Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P008_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-163 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P008Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P008Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P008 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P008]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P008 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P008 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P008Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P008Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P008_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P008] using h

theorem momentScalarGrow2622K06P008_radius_le :
    (momentScalarGrow2622K06P008Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P008Expected]

end ConnesWeilRH.Dev
