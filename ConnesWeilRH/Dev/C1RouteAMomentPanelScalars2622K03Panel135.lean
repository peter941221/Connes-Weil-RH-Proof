import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P135 : ℚ := ((-72814911632652152929411916496165910773409113678905225 : ℚ) / 1931557101437454569270944967038657545852771847110656)

def momentPanelGrowth2622K03P135 : ℚ := ((52872877867662535350798454931087112578690356688488475 : ℚ) / 118285447547296296326194191441965784215899429920571392)

theorem momentPanelPhase_owner2622K03P135 :
    (momentPanelPhase2622K03P135 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (91 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P135, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P135 :
    (momentPanelGrowth2622K03P135 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (91 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P135, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P135Input : RatPair2542 := (momentPanelPhase2622K03P135 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P135Expected : RatState2542 :=
  ((((90734799030179573577400714575000485425336731941441436529020661025399674899066421 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((57512080023586189155343176216331 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K03P135_replay :
    compactExp2620 momentScalarAmp2622K03P135Input 20 = momentScalarAmp2622K03P135Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P135_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (91 / 200) 0) -
      (momentScalarAmp2622K03P135Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P135Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P135 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P135]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P135 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P135 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P135Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P135Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P135_replay] at h
  simpa only [momentPanelPhase_owner2622K03P135] using h

theorem momentScalarAmp2622K03P135_radius_le :
    (momentScalarAmp2622K03P135Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P135Expected]

def momentScalarGrow2622K03P135Input : RatPair2542 := (momentPanelGrowth2622K03P135 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P135Expected : RatState2542 :=
  ((((1669919811172808819788937393867322058573194610302679524108406488182852422929420431468934115681171 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2116873948570953529548372967001453806329502551575 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P135_replay :
    compactExp2620 momentScalarGrow2622K03P135Input 20 = momentScalarGrow2622K03P135Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P135_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (91 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P135Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P135Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P135 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P135]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P135 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P135 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P135Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P135Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P135_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P135] using h

theorem momentScalarGrow2622K03P135_radius_le :
    (momentScalarGrow2622K03P135Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P135Expected]

end ConnesWeilRH.Dev
