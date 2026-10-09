import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P087 : ℚ := ((-916548699842355166203017952915920012196150793662907 : ℚ) / 30428920808491064664162656868663236307680158023680)

def momentPanelGrowth2622K02P087 : ℚ := ((839377513779913744371153654406272457247578266889371999 : ℚ) / 14246798029297202450998847119161212992283181501015654400)

theorem momentPanelPhase_owner2622K02P087 :
    (momentPanelPhase2622K02P087 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-1 / 40) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P087, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P087 :
    (momentPanelGrowth2622K02P087 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-1 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P087, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P087Input : RatPair2542 := (momentPanelPhase2622K02P087 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P087Expected : RatState2542 :=
  ((((44275787030416564487679567265912524724457282638701405035654516595507779579351643439 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((224511361151695348357881182983756431 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P087_replay :
    compactExp2620 momentScalarAmp2622K02P087Input 20 = momentScalarAmp2622K02P087Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P087_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-1 / 40) 0) -
      (momentScalarAmp2622K02P087Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P087Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P087 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P087]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P087 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P087 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P087Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P087Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P087_replay] at h
  simpa only [momentPanelPhase_owner2622K02P087] using h

theorem momentScalarAmp2622K02P087_radius_le :
    (momentScalarAmp2622K02P087Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P087Expected]

def momentScalarGrow2622K02P087Input : RatPair2542 := (momentPanelGrowth2622K02P087 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P087Expected : RatState2542 :=
  ((((283201741976882670466336397474254268382105463806226087375939989323017059128746373288191624572883 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((1436003352125179397610321602370562432157625855529 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P087_replay :
    compactExp2620 momentScalarGrow2622K02P087Input 20 = momentScalarGrow2622K02P087Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P087_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-1 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P087Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P087Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P087 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P087]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P087 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P087 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P087Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P087Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P087_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P087] using h

theorem momentScalarGrow2622K02P087_radius_le :
    (momentScalarGrow2622K02P087Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P087Expected]

end ConnesWeilRH.Dev
