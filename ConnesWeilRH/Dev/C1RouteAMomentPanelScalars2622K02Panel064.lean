import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P064 : ℚ := ((-353669262491838561077084412646060926646003599134662971 : ℚ) / 10675527291902038718339767394288333721115668198195200)

def momentPanelGrowth2622K02P064 : ℚ := ((56954239062844140016917092116601763937183793094294973 : ℚ) / 258501246680902935909431379014932274757965770968268800)

theorem momentPanelPhase_owner2622K02P064 :
    (momentPanelPhase2622K02P064 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-51 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P064, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P064 :
    (momentPanelGrowth2622K02P064 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-51 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P064, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P064Input : RatPair2542 := (momentPanelPhase2622K02P064 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P064Expected : RatState2542 :=
  ((((4373590966456514361735922033478947731496836057386465830100801753391178234082266761 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((5544360382138371813699250350926935 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P064_replay :
    compactExp2620 momentScalarAmp2622K02P064Input 20 = momentScalarAmp2622K02P064Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P064_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-51 / 200) 0) -
      (momentScalarAmp2622K02P064Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P064Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P064 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P064]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P064 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P064 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P064Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P064Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P064_replay] at h
  simpa only [momentPanelPhase_owner2622K02P064] using h

theorem momentScalarAmp2622K02P064_radius_le :
    (momentScalarAmp2622K02P064Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P064Expected]

def momentScalarGrow2622K02P064Input : RatPair2542 := (momentPanelGrowth2622K02P064 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P064Expected : RatState2542 :=
  ((((2662468408557415323771417145780223612485066489502840390467179868751783010860247946638119106016871 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3375078967031197002411832901218122242855741517981 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P064_replay :
    compactExp2620 momentScalarGrow2622K02P064Input 20 = momentScalarGrow2622K02P064Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P064_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-51 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P064Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P064Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P064 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P064]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P064 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P064 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P064Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P064Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P064_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P064] using h

theorem momentScalarGrow2622K02P064_radius_le :
    (momentScalarGrow2622K02P064Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P064Expected]

end ConnesWeilRH.Dev
