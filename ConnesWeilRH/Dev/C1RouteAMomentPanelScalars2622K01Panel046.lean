import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P046 : ℚ := ((-85822325306431966043012907193677250367065503451320681 : ℚ) / 2314353496107349245130063613760828838401442788147200)

def momentPanelGrowth2622K01P046 : ℚ := ((19252604658350945847433260545294751688079570429179 : ℚ) / 47206217436249623066002808439542051635859344588800)

theorem momentPanelPhase_owner2622K01P046 :
    (momentPanelPhase2622K01P046 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-87 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P046, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P046 :
    (momentPanelGrowth2622K01P046 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-87 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P046, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P046Input : RatPair2542 := (momentPanelPhase2622K01P046 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P046Expected : RatState2542 :=
  ((((83904447889155188574254900825690153073246313021809209238135166473169104151270217 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((106365286453311828531700083148101 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P046_replay :
    compactExp2620 momentScalarAmp2622K01P046Input 20 = momentScalarAmp2622K01P046Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P046_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-87 / 200) 0) -
      (momentScalarAmp2622K01P046Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P046Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P046 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P046]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P046 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P046 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P046Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P046Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P046_replay] at h
  simpa only [momentPanelPhase_owner2622K01P046] using h

theorem momentScalarAmp2622K01P046_radius_le :
    (momentScalarAmp2622K01P046Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P046Expected]

def momentScalarGrow2622K01P046Input : RatPair2542 := (momentPanelGrowth2622K01P046 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P046Expected : RatState2542 :=
  ((((802900032110678016611253892195311887617611544005031788724685651109429558345995948890502919695365 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1017796311759511167983406712187496815740391129185 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K01P046_replay :
    compactExp2620 momentScalarGrow2622K01P046Input 20 = momentScalarGrow2622K01P046Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P046_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-87 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P046Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P046Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P046 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P046]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P046 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P046 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P046Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P046Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P046_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P046] using h

theorem momentScalarGrow2622K01P046_radius_le :
    (momentScalarGrow2622K01P046Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P046Expected]

end ConnesWeilRH.Dev
