import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P116 : ℚ := ((-110345831392720194645019228505552610845375583788412161 : ℚ) / 3538717929295156929095914232653078241147381979545600)

def momentPanelGrowth2622K02P116 : ℚ := ((2813687515176782750745923834979445393848176081315285439 : ℚ) / 12267399585200244106514828406426608369458859987068518400)

theorem momentPanelPhase_owner2622K02P116 :
    (momentPanelPhase2622K02P116 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (53 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P116, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P116 :
    (momentPanelGrowth2622K02P116 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (53 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P116, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P116Input : RatPair2542 := (momentPanelPhase2622K02P116 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P116Expected : RatState2542 :=
  ((((61268950131595727310454135995102632798845332589337417900227772408811327612091251851 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((77669931117191960959685907900870543 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P116_replay :
    compactExp2620 momentScalarAmp2622K02P116Input 20 = momentScalarAmp2622K02P116Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P116_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (53 / 200) 0) -
      (momentScalarAmp2622K02P116Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P116Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P116 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P116]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P116 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P116 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P116Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P116Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P116_replay] at h
  simpa only [momentPanelPhase_owner2622K02P116] using h

theorem momentScalarAmp2622K02P116_radius_le :
    (momentScalarAmp2622K02P116Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P116Expected]

def momentScalarGrow2622K02P116Input : RatPair2542 := (momentPanelGrowth2622K02P116 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P116Expected : RatState2542 :=
  ((((671660339158704609457345460045805859952812520209694826538937639600898293592142585964870062389109 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3405721783376628735267709298061503201704643480893 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P116_replay :
    compactExp2620 momentScalarGrow2622K02P116Input 20 = momentScalarGrow2622K02P116Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P116_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (53 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P116Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P116Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P116 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P116]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P116 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P116 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P116Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P116Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P116_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P116] using h

theorem momentScalarGrow2622K02P116_radius_le :
    (momentScalarGrow2622K02P116Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P116Expected]

end ConnesWeilRH.Dev
