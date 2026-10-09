import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P003 : ℚ := ((-117568688250319586225609462725170390397579075762233719 : ℚ) / 958254100882781464142533199888391034567376083353600)

def momentPanelGrowth2622K02P003 : ℚ := ((7484717758636387049825302300898704120582658924773624719 : ℚ) / 843469275169366617264289714909981782668443707139686400)

theorem momentPanelPhase_owner2622K02P003 :
    (momentPanelPhase2622K02P003 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-173 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P003, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P003 :
    (momentPanelGrowth2622K02P003 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-173 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P003, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P003Input : RatPair2542 := (momentPanelPhase2622K02P003 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P003Expected : RatState2542 :=
  ((((5555912185392520170894153728491840220149539 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P003_replay :
    compactExp2620 momentScalarAmp2622K02P003Input 20 = momentScalarAmp2622K02P003Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P003_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-173 / 200) 0) -
      (momentScalarAmp2622K02P003Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P003Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P003 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P003]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P003 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P003 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P003Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P003Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P003_replay] at h
  simpa only [momentPanelPhase_owner2622K02P003] using h

theorem momentScalarAmp2622K02P003_radius_le :
    (momentScalarAmp2622K02P003Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P003Expected]

def momentScalarGrow2622K02P003Input : RatPair2542 := (momentPanelGrowth2622K02P003 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P003Expected : RatState2542 :=
  ((((15254927445594660243694134801259484357159761963690048614605155162263510045424865427446931504014227035 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((19337754283557161944254090588526975625285936229142093 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P003_replay :
    compactExp2620 momentScalarGrow2622K02P003Input 20 = momentScalarGrow2622K02P003Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P003_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-173 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P003Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P003Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P003 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P003]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P003 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P003 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P003Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P003Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P003_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P003] using h

theorem momentScalarGrow2622K02P003_radius_le :
    (momentScalarGrow2622K02P003Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 68 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P003Expected]

end ConnesWeilRH.Dev
