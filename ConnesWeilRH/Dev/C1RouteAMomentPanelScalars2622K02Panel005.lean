import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P005 : ℚ := ((-117940018817720668856452230910065548928252011672214563 : ℚ) / 1088419090457565005295048880302184991005482575462400)

def momentPanelGrowth2622K02P005 : ℚ := ((3906079005452502132447977288398076140586341855407653 : ℚ) / 586170627394337723150638047652907652512394038476800)

theorem momentPanelPhase_owner2622K02P005 :
    (momentPanelPhase2622K02P005 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-169 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P005, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P005 :
    (momentPanelGrowth2622K02P005 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-169 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P005, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P005Input : RatPair2542 := (momentPanelPhase2622K02P005 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P005Expected : RatState2542 :=
  ((((18615599392983494403480781279678076394615333319243 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1208925819614629174706195 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K02P005_replay :
    compactExp2620 momentScalarAmp2622K02P005Input 20 = momentScalarAmp2622K02P005Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P005_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-169 / 200) 0) -
      (momentScalarAmp2622K02P005Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P005Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P005 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P005]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P005 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P005 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P005Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P005Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P005_replay] at h
  simpa only [momentPanelPhase_owner2622K02P005] using h

theorem momentScalarAmp2622K02P005_radius_le :
    (momentScalarAmp2622K02P005Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P005Expected]

def momentScalarGrow2622K02P005Input : RatPair2542 := (momentPanelGrowth2622K02P005 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P005Expected : RatState2542 :=
  ((((836733153358220941180928938800233827197817204518905925051441295478901301368530207330276814208936229 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2121357086857049135944520112050666826374510226028795 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P005_replay :
    compactExp2620 momentScalarGrow2622K02P005Input 20 = momentScalarGrow2622K02P005Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P005_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-169 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P005Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P005Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P005 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P005]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P005 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P005 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P005Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P005Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P005_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P005] using h

theorem momentScalarGrow2622K02P005_radius_le :
    (momentScalarGrow2622K02P005Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P005Expected]

end ConnesWeilRH.Dev
