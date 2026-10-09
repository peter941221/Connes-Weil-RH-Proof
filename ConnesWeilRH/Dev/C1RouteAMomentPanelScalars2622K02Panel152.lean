import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P152 : ℚ := ((-6928218368295875283004408008917619377402473165745 : ℚ) / 148433760041419827630061740822747494183805648896)

def momentPanelGrowth2622K02P152 : ℚ := ((5607240797980157143684333226779956382718057642724537519 : ℚ) / 5191322466413386322129767429363367806533932402763366400)

theorem momentPanelPhase_owner2622K02P152 :
    (momentPanelPhase2622K02P152 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (5 / 8) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P152, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P152 :
    (momentPanelGrowth2622K02P152 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (5 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P152, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P152Input : RatPair2542 := (momentPanelPhase2622K02P152 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P152Expected : RatState2542 :=
  ((((178859175915944220841521035697587437366744831305686399173188645699871072615 : ℚ) / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384), 0), ((14513844056696977602539018519 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P152_replay :
    compactExp2620 momentScalarAmp2622K02P152Input 20 = momentScalarAmp2622K02P152Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P152_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (5 / 8) 0) -
      (momentScalarAmp2622K02P152Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P152Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P152 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P152]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P152 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P152 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P152Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P152Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P152_replay] at h
  simpa only [momentPanelPhase_owner2622K02P152] using h

theorem momentScalarAmp2622K02P152_radius_le :
    (momentScalarAmp2622K02P152Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 92 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P152Expected]

def momentScalarGrow2622K02P152Input : RatPair2542 := (momentPanelGrowth2622K02P152 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P152Expected : RatState2542 :=
  ((((6290539535247928902188796064562644768553894781366230611052706454379041391212067483389052467540143 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7974198003544053819565998424694493104776586656735 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P152_replay :
    compactExp2620 momentScalarGrow2622K02P152Input 20 = momentScalarGrow2622K02P152Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P152_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (5 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P152Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P152Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P152 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P152]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P152 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P152 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P152Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P152Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P152_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P152] using h

theorem momentScalarGrow2622K02P152_radius_le :
    (momentScalarGrow2622K02P152Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P152Expected]

end ConnesWeilRH.Dev
