import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P155 : ℚ := ((-72805404121374018979256944779996867163714853081882225 : ℚ) / 1390801495625020489535581578933632828580076806209536)

def momentPanelGrowth2622K03P155 : ℚ := ((226614393565049918941671361159406072619412361091589425 : ℚ) / 181858393831029910550812400677270931611025554649645056)

theorem momentPanelPhase_owner2622K03P155 :
    (momentPanelPhase2622K03P155 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (131 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P155, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P155 :
    (momentPanelGrowth2622K03P155 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (131 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P155, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P155Input : RatPair2542 := (momentPanelPhase2622K03P155 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P155Expected : RatState2542 :=
  ((((19688208135468999324097290190946356362993923845513383775393530079838322701 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3270992583960304087378163 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K03P155_replay :
    compactExp2620 momentScalarAmp2622K03P155Input 20 = momentScalarAmp2622K03P155Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P155_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (131 / 200) 0) -
      (momentScalarAmp2622K03P155Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P155Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P155 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P155]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P155 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P155 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P155Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P155Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P155_replay] at h
  simpa only [momentPanelPhase_owner2622K03P155] using h

theorem momentScalarAmp2622K03P155_radius_le :
    (momentScalarAmp2622K03P155Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 94 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P155Expected]

def momentScalarGrow2622K03P155Input : RatPair2542 := (momentPanelGrowth2622K03P155 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P155Expected : RatState2542 :=
  ((((7426334658574988187671479899422017827354171660791335982458836441078392833358967423075539129925325 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1176748300008376763108657026014486400078050685849 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K03P155_replay :
    compactExp2620 momentScalarGrow2622K03P155Input 20 = momentScalarGrow2622K03P155Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P155_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (131 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P155Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P155Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P155 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P155]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P155 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P155 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P155Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P155Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P155_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P155] using h

theorem momentScalarGrow2622K03P155_radius_le :
    (momentScalarGrow2622K03P155Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P155Expected]

end ConnesWeilRH.Dev
