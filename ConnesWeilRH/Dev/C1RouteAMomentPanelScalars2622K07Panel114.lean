import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P114 : ℚ := ((-30440596862495383705542108132439339225 : ℚ) / 1016797758250265541693323601470554112)

def momentPanelGrowth2622K07P114 : ℚ := ((3824288895587729592512813729388173 : ℚ) / 15211807202738752817960438464512000)

theorem momentPanelPhase_owner2622K07P114 :
    (momentPanelPhase2622K07P114 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (49 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P114, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P114 :
    (momentPanelGrowth2622K07P114 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (49 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P114, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P114Input : RatPair2542 := (momentPanelPhase2622K07P114 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P114Expected : RatState2542 :=
  ((((53180960427322191960878984032658269198437887623459084472649138969482881542998613703 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((269667204739460037188395982732426975 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P114_replay :
    compactExp2620 momentScalarAmp2622K07P114Input 20 = momentScalarAmp2622K07P114Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P114_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (49 / 200) 0) -
      (momentScalarAmp2622K07P114Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P114Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P114 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P114]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P114 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P114 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P114Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P114Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P114_replay] at h
  simpa only [momentPanelPhase_owner2622K07P114] using h

theorem momentScalarAmp2622K07P114_radius_le :
    (momentScalarAmp2622K07P114Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P114Expected]

def momentScalarGrow2622K07P114Input : RatPair2542 := (momentPanelGrowth2622K07P114 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P114Expected : RatState2542 :=
  ((((2746511383223084100771294448908294035421508797432833289780877859981417513206313879033976669283975 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((870403992184265467539292082759804856524952583153 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K07P114_replay :
    compactExp2620 momentScalarGrow2622K07P114Input 20 = momentScalarGrow2622K07P114Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P114_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (49 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P114Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P114Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P114 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P114]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P114 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P114 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P114Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P114Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P114_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P114] using h

theorem momentScalarGrow2622K07P114_radius_le :
    (momentScalarGrow2622K07P114Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P114Expected]

end ConnesWeilRH.Dev
