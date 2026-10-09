import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P168 : ℚ := ((-109491974153631225834818075338173473918536854675399449 : ℚ) / 1460645288715279342275049861134613322574102895001600)

def momentPanelGrowth2622K02P168 : ℚ := ((2282535435787636409364512331221012373451140073005287333 : ℚ) / 672237516833277410070131548982829722873141893319884800)

theorem momentPanelPhase_owner2622K02P168 :
    (momentPanelPhase2622K02P168 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (157 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P168, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P168 :
    (momentPanelGrowth2622K02P168 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (157 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P168, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P168Input : RatPair2542 := (momentPanelPhase2622K02P168 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P168Expected : RatState2542 :=
  ((((1486718042399817641181262033453843788530885944534184950632972385 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((302231455846044202617533 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K02P168_replay :
    compactExp2620 momentScalarAmp2622K02P168Input 20 = momentScalarAmp2622K02P168Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P168_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (157 / 200) 0) -
      (momentScalarAmp2622K02P168Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P168Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P168 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P168]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P168 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P168 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P168Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P168Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P168_replay] at h
  simpa only [momentPanelPhase_owner2622K02P168] using h

theorem momentScalarAmp2622K02P168_radius_le :
    (momentScalarAmp2622K02P168Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P168Expected]

def momentScalarGrow2622K02P168Input : RatPair2542 := (momentPanelGrowth2622K02P168 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P168Expected : RatState2542 :=
  ((((15927775891943227688121745659090942165103697700308042197805234464213648842808020517243171644691401 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((40381578578255088490806309984055813177846810627325 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P168_replay :
    compactExp2620 momentScalarGrow2622K02P168Input 20 = momentScalarGrow2622K02P168Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P168_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (157 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P168Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P168Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P168 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P168]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P168 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P168 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P168Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P168Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P168_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P168] using h

theorem momentScalarGrow2622K02P168_radius_le :
    (momentScalarGrow2622K02P168Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P168Expected]

end ConnesWeilRH.Dev
