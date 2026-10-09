import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P170 : ℚ := ((-72870769613446354581388950267754060331274398420857475 : ℚ) / 857353397999240924391236614992189526405661428023296)

def momentPanelGrowth2622K03P170 : ℚ := ((4442509251927624543199288733130614894294966640310204425 : ℚ) / 1080298256609735843230050105529196964406764386287353856)

theorem momentPanelPhase_owner2622K03P170 :
    (momentPanelPhase2622K03P170 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (161 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P170, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P170 :
    (momentPanelGrowth2622K03P170 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (161 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P170, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P170Input : RatPair2542 := (momentPanelPhase2622K03P170 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P170Expected : RatState2542 :=
  ((((4078967630288436517368618525800636268806328435287090887223 : ℚ) / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384), 0), ((2417851639229589303096919 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P170_replay :
    compactExp2620 momentScalarAmp2622K03P170Input 20 = momentScalarAmp2622K03P170Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P170_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (161 / 200) 0) -
      (momentScalarAmp2622K03P170Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P170Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P170 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P170]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P170 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P170 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P170Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P170Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P170_replay] at h
  simpa only [momentPanelPhase_owner2622K03P170] using h

theorem momentScalarAmp2622K03P170_radius_le :
    (momentScalarAmp2622K03P170Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P170Expected]

def momentScalarGrow2622K03P170Input : RatPair2542 := (momentPanelGrowth2622K03P170 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P170Expected : RatState2542 :=
  ((((32620251795306072272332212882254510509997209652460022564037176797577144854685522228217399602856621 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((165403678391275218077348888988359928327966024593611 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P170_replay :
    compactExp2620 momentScalarGrow2622K03P170Input 20 = momentScalarGrow2622K03P170Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P170_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (161 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P170Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P170Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P170 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P170]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P170 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P170 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P170Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P170Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P170_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P170] using h

theorem momentScalarGrow2622K03P170_radius_le :
    (momentScalarGrow2622K03P170Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P170Expected]

end ConnesWeilRH.Dev
