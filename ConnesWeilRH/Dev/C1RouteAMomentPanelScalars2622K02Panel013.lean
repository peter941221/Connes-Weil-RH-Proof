import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P013 : ℚ := ((-357351723150774867887324985427419391580724391712060217 : ℚ) / 4735893293936916077327604503827314761545229847756800)

def momentPanelGrowth2622K02P013 : ℚ := ((2230197270923795047372980486828660600786979638716850613 : ℚ) / 788461150945709135104469892047041010819061716405452800)

theorem momentPanelPhase_owner2622K02P013 :
    (momentPanelPhase2622K02P013 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-153 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P013, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P013 :
    (momentPanelGrowth2622K02P013 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-153 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P013, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P013Input : RatPair2542 := (momentPanelPhase2622K02P013 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P013Expected : RatState2542 :=
  ((((1813132870169881878942296042439296096419971686721527544305135423 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851643826427293559861 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P013_replay :
    compactExp2620 momentScalarAmp2622K02P013Input 20 = momentScalarAmp2622K02P013Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P013_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-153 / 200) 0) -
      (momentScalarAmp2622K02P013Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P013Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P013 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P013]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P013 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P013 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P013Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P013Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P013_replay] at h
  simpa only [momentPanelPhase_owner2622K02P013] using h

theorem momentScalarAmp2622K02P013_radius_le :
    (momentScalarAmp2622K02P013Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P013Expected]

def momentScalarGrow2622K02P013Input : RatPair2542 := (momentPanelGrowth2622K02P013 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P013Expected : RatState2542 :=
  ((((36142632423922893462832787167747370292009705982336458826281376099505854930141659821052647507462833 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((45816106096441998596362914496395914971975231970891 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P013_replay :
    compactExp2620 momentScalarGrow2622K02P013Input 20 = momentScalarGrow2622K02P013Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P013_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-153 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P013Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P013Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P013 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P013]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P013 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P013 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P013Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P013Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P013_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P013] using h

theorem momentScalarGrow2622K02P013_radius_le :
    (momentScalarGrow2622K02P013Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P013Expected]

end ConnesWeilRH.Dev
