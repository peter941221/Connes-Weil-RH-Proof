import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P173 : ℚ := ((-110245827255688958330238548369266024213615687257749459 : ℚ) / 1152359787090792007966460091733522373115429624217600)

def momentPanelGrowth2622K02P173 : ℚ := ((442132756694713492236513908043797662323513028792191 : ℚ) / 75501402944145277707983327783878292714647296409600)

theorem momentPanelPhase_owner2622K02P173 :
    (momentPanelPhase2622K02P173 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (167 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P173, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P173 :
    (momentPanelGrowth2622K02P173 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (167 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P173, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P173Input : RatPair2542 := (momentPanelPhase2622K02P173 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P173Expected : RatState2542 :=
  ((((6036829804988422709979097147309972763678923606649221385 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258357073771 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P173_replay :
    compactExp2620 momentScalarAmp2622K02P173Input 20 = momentScalarAmp2622K02P173Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P173_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (167 / 200) 0) -
      (momentScalarAmp2622K02P173Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P173Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P173 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P173]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P173 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P173 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P173Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P173Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P173_replay] at h
  simpa only [momentPanelPhase_owner2622K02P173] using h

theorem momentScalarAmp2622K02P173_radius_le :
    (momentScalarAmp2622K02P173Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P173Expected]

def momentScalarGrow2622K02P173Input : RatPair2542 := (momentPanelGrowth2622K02P173 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P173Expected : RatState2542 :=
  ((((373058729200164764107125009551075642504482337839041721673606382604898248468852653144616729881398465 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((945810961922146865880303006015111959440824959237783 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P173_replay :
    compactExp2620 momentScalarGrow2622K02P173Input 20 = momentScalarGrow2622K02P173Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P173_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (167 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P173Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P173Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P173 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P173]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P173 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P173 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P173Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P173Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P173_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P173] using h

theorem momentScalarGrow2622K02P173_radius_le :
    (momentScalarGrow2622K02P173Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P173Expected]

end ConnesWeilRH.Dev
