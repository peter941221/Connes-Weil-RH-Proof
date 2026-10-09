import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K08
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K08P064 : ℚ := ((-2463847307156209832186091097625176196781 : ℚ) / 75854183676696882218520325084571238400)

def momentPanelGrowth2622K08P064 : ℚ := ((358036923284554986369608784326821583003 : ℚ) / 1836761830140452900006887510748273049600)

theorem momentPanelPhase_owner2622K08P064 :
    (momentPanelPhase2622K08P064 : ℝ) = momentPhase2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2)) (-51 / 200) 0 := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelPhase2622K08P064, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K08P064 :
    (momentPanelGrowth2622K08P064 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2))
      (-51 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelGrowth2622K08P064, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K08P064Input : RatPair2542 := (momentPanelPhase2622K08P064 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K08P064Expected : RatState2542 :=
  ((((16715590113659431917922930763412633213635618123765189930274251188994878632386194733 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((21190184233752932676170503304703099 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K08P064_replay :
    compactExp2620 momentScalarAmp2622K08P064Input 20 = momentScalarAmp2622K08P064Expected := by
  decide +kernel

theorem momentScalarAmp2622K08P064_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2)) (-51 / 200) 0) -
      (momentScalarAmp2622K08P064Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K08P064Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K08P064 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelPhase2622K08P064]
  have h := compactExp_real_error2620 momentPanelPhase2622K08P064 20 hsmall
  change |Real.exp (momentPanelPhase2622K08P064 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K08P064Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K08P064Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K08P064_replay] at h
  simpa only [momentPanelPhase_owner2622K08P064] using h

theorem momentScalarAmp2622K08P064_radius_le :
    (momentScalarAmp2622K08P064Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentScalarAmp2622K08P064Expected]

def momentScalarGrow2622K08P064Input : RatPair2542 := (momentPanelGrowth2622K08P064 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K08P064Expected : RatState2542 :=
  ((((2595702481164119742398791860776797037425711210420933040219975044871098651823450218454274721855443 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((822610799143563900074743042554960584562534066179 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K08P064_replay :
    compactExp2620 momentScalarGrow2622K08P064Input 20 = momentScalarGrow2622K08P064Expected := by
  decide +kernel

theorem momentScalarGrow2622K08P064_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2)) (-51 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K08P064Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K08P064Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K08P064 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelGrowth2622K08P064]
  have h := compactExp_real_error2620 momentPanelGrowth2622K08P064 20 hsmall
  change |Real.exp (momentPanelGrowth2622K08P064 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K08P064Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K08P064Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K08P064_replay] at h
  simpa only [momentPanelGrowth_owner2622K08P064] using h

theorem momentScalarGrow2622K08P064_radius_le :
    (momentScalarGrow2622K08P064Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentScalarGrow2622K08P064Expected]

end ConnesWeilRH.Dev
