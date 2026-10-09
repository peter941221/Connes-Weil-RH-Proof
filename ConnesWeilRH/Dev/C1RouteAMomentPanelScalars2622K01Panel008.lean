import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P008 : ℚ := ((-28593439411503103364154210026402898600551368064538023 : ℚ) / 319489396012229119374897314261269486279277831782400)

def momentPanelGrowth2622K01P008 : ℚ := ((36588077521908685830013322415793961526998205162531251 : ℚ) / 7977850746726186298154474626282606726460229235507200)

theorem momentPanelPhase_owner2622K01P008 :
    (momentPanelPhase2622K01P008 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-163 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P008, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P008 :
    (momentPanelGrowth2622K01P008 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-163 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P008, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P008Input : RatPair2542 := (momentPanelPhase2622K01P008 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P008Expected : RatState2542 :=
  ((((723358525677658200665108411025736018789262766347054560021 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1208925819614631008883439 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P008_replay :
    compactExp2620 momentScalarAmp2622K01P008Input 20 = momentScalarAmp2622K01P008Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P008_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-163 / 200) 0) -
      (momentScalarAmp2622K01P008Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P008Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P008 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P008]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P008 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P008 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P008Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P008Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P008_replay] at h
  simpa only [momentPanelPhase_owner2622K01P008] using h

theorem momentScalarAmp2622K01P008_radius_le :
    (momentScalarAmp2622K01P008Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P008Expected]

def momentScalarGrow2622K01P008Input : RatPair2542 := (momentPanelGrowth2622K01P008 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P008Expected : RatState2542 :=
  ((((104793211589548776866848688571723014571726275814014823158557858556730587086207541738200277582278361 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((132840596558753394813430645298148884056469960531313 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P008_replay :
    compactExp2620 momentScalarGrow2622K01P008Input 20 = momentScalarGrow2622K01P008Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P008_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-163 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P008Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P008Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P008 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P008]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P008 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P008 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P008Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P008Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P008_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P008] using h

theorem momentScalarGrow2622K01P008_radius_le :
    (momentScalarGrow2622K01P008Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P008Expected]

end ConnesWeilRH.Dev
