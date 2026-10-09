import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P011 : ℚ := ((-118867656679322355134507679773745747902702605164600551 : ℚ) / 1460645288715279342275049861134613322574102895001600)

def momentPanelGrowth2622K02P011 : ℚ := ((2282535435787636409364512331221012373451140073005287333 : ℚ) / 672237516833277410070131548982829722873141893319884800)

theorem momentPanelPhase_owner2622K02P011 :
    (momentPanelPhase2622K02P011 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-157 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P011, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P011 :
    (momentPanelGrowth2622K02P011 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-157 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P011, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P011Input : RatPair2542 := (momentPanelPhase2622K02P011 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P011Expected : RatState2542 :=
  ((((1212053190041478939461074043474165828994093972446555122755563 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((37778931863149234270993 : ℚ) / 40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584))

theorem momentScalarAmp2622K02P011_replay :
    compactExp2620 momentScalarAmp2622K02P011Input 20 = momentScalarAmp2622K02P011Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P011_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-157 / 200) 0) -
      (momentScalarAmp2622K02P011Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P011Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P011 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P011]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P011 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P011 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P011Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P011Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P011_replay] at h
  simpa only [momentPanelPhase_owner2622K02P011] using h

theorem momentScalarAmp2622K02P011_radius_le :
    (momentScalarAmp2622K02P011Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P011Expected]

def momentScalarGrow2622K02P011Input : RatPair2542 := (momentPanelGrowth2622K02P011 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P011Expected : RatState2542 :=
  ((((15927775891943227688121745659090942165103697700308042197805234464213648842808020517243171644691401 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((40381578578255088490806309984055813177846810627325 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P011_replay :
    compactExp2620 momentScalarGrow2622K02P011Input 20 = momentScalarGrow2622K02P011Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P011_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-157 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P011Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P011Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P011 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P011]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P011 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P011 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P011Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P011Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P011_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P011] using h

theorem momentScalarGrow2622K02P011_radius_le :
    (momentScalarGrow2622K02P011Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P011Expected]

end ConnesWeilRH.Dev
