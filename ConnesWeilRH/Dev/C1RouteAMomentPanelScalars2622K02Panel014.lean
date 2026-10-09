import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P014 : ℚ := ((-119231273075340820516655147507002975080406315773289757 : ℚ) / 1636482204456653599621430692570791123376457279078400)

def momentPanelGrowth2622K02P014 : ℚ := ((134528862371109206730700448230664382544503640097477 : ℚ) / 51809091245226343682415780691016673450693702451200)

theorem momentPanelPhase_owner2622K02P014 :
    (momentPanelPhase2622K02P014 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-151 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P014, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P014 :
    (momentPanelGrowth2622K02P014 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-151 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P014, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P014Input : RatPair2542 := (momentPanelPhase2622K02P014 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P014Expected : RatState2542 :=
  ((((48713701604395264453293273939297098735978106390113562802384676865 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((151115731311593938875417 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K02P014_replay :
    compactExp2620 momentScalarAmp2622K02P014Input 20 = momentScalarAmp2622K02P014Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P014_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-151 / 200) 0) -
      (momentScalarAmp2622K02P014Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P014Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P014 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P014]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P014 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P014 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P014Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P014Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P014_replay] at h
  simpa only [momentPanelPhase_owner2622K02P014] using h

theorem momentScalarAmp2622K02P014_radius_le :
    (momentScalarAmp2622K02P014Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P014Expected]

def momentScalarGrow2622K02P014Input : RatPair2542 := (momentPanelGrowth2622K02P014 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P014Expected : RatState2542 :=
  ((((14330759355983683430609869529782558359336238550404047612240199860139009717918703459915037685128295 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((18166350713293990380554487802500438438152037373889 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P014_replay :
    compactExp2620 momentScalarGrow2622K02P014Input 20 = momentScalarGrow2622K02P014Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P014_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-151 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P014Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P014Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P014 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P014]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P014 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P014 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P014Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P014Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P014_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P014] using h

theorem momentScalarGrow2622K02P014_radius_le :
    (momentScalarGrow2622K02P014Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P014Expected]

end ConnesWeilRH.Dev
