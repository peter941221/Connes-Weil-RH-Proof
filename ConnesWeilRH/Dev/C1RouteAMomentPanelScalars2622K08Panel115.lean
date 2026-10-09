import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K08
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K08P115 : ℚ := ((-2403930997720191069561249211018663803219 : ℚ) / 75854183676696882218520325084571238400)

def momentPanelGrowth2622K08P115 : ℚ := ((358036923284554986369608784326821583003 : ℚ) / 1836761830140452900006887510748273049600)

theorem momentPanelPhase_owner2622K08P115 :
    (momentPanelPhase2622K08P115 : ℝ) = momentPhase2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2)) (51 / 200) 0 := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelPhase2622K08P115, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K08P115 :
    (momentPanelGrowth2622K08P115 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2))
      (51 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelGrowth2622K08P115, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K08P115Input : RatPair2542 := (momentPanelPhase2622K08P115 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K08P115Expected : RatState2542 :=
  ((((36826946670181972654848106022142501985433272375419709150697784627672093079942270507 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((46685112012425759554907109153938079 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K08P115_replay :
    compactExp2620 momentScalarAmp2622K08P115Input 20 = momentScalarAmp2622K08P115Expected := by
  decide +kernel

theorem momentScalarAmp2622K08P115_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2)) (51 / 200) 0) -
      (momentScalarAmp2622K08P115Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K08P115Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K08P115 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelPhase2622K08P115]
  have h := compactExp_real_error2620 momentPanelPhase2622K08P115 20 hsmall
  change |Real.exp (momentPanelPhase2622K08P115 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K08P115Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K08P115Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K08P115_replay] at h
  simpa only [momentPanelPhase_owner2622K08P115] using h

theorem momentScalarAmp2622K08P115_radius_le :
    (momentScalarAmp2622K08P115Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentScalarAmp2622K08P115Expected]

def momentScalarGrow2622K08P115Input : RatPair2542 := (momentPanelGrowth2622K08P115 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K08P115Expected : RatState2542 :=
  ((((2595702481164119742398791860776797037425711210420933040219975044871098651823450218454274721855443 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((822610799143563900074743042554960584562534066179 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K08P115_replay :
    compactExp2620 momentScalarGrow2622K08P115Input 20 = momentScalarGrow2622K08P115Expected := by
  decide +kernel

theorem momentScalarGrow2622K08P115_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2)) (51 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K08P115Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K08P115Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K08P115 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelGrowth2622K08P115]
  have h := compactExp_real_error2620 momentPanelGrowth2622K08P115 20 hsmall
  change |Real.exp (momentPanelGrowth2622K08P115 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K08P115Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K08P115Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K08P115_replay] at h
  simpa only [momentPanelGrowth_owner2622K08P115] using h

theorem momentScalarGrow2622K08P115_radius_le :
    (momentScalarGrow2622K08P115Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentScalarGrow2622K08P115Expected]

end ConnesWeilRH.Dev
