import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P119 : ℚ := ((-28497235294347408624707290561589220129227071042517489 : ℚ) / 868694308165482481606125755305435214759358732697600)

def momentPanelGrowth2622K01P119 : ℚ := ((64776346035415004940020811167843898070198521136713 : ℚ) / 295475953582451344376091652825281730609638119833600)

theorem momentPanelPhase_owner2622K01P119 :
    (momentPanelPhase2622K01P119 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (59 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P119, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P119 :
    (momentPanelGrowth2622K01P119 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (59 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P119, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P119Input : RatPair2542 := (momentPanelPhase2622K01P119 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P119Expected : RatState2542 :=
  ((((12097868486836714645842425569380997998475817494828074542651755800195015018760177927 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((958521877568160915790100707991457 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K01P119_replay :
    compactExp2620 momentScalarAmp2622K01P119Input 20 = momentScalarAmp2622K01P119Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P119_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (59 / 200) 0) -
      (momentScalarAmp2622K01P119Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P119Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P119 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P119]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P119 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P119 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P119Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P119Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P119_replay] at h
  simpa only [momentPanelPhase_owner2622K01P119] using h

theorem momentScalarAmp2622K01P119_radius_le :
    (momentScalarAmp2622K01P119Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P119Expected]

def momentScalarGrow2622K01P119Input : RatPair2542 := (momentPanelGrowth2622K01P119 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P119Expected : RatState2542 :=
  ((((2659547470061922495469011902077989549278821057163127706151239631984449106135325046060371909499391 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((421422030237678218037219002605586794570464185697 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K01P119_replay :
    compactExp2620 momentScalarGrow2622K01P119Input 20 = momentScalarGrow2622K01P119Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P119_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (59 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P119Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P119Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P119 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P119]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P119 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P119 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P119Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P119Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P119_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P119] using h

theorem momentScalarGrow2622K01P119_radius_le :
    (momentScalarGrow2622K01P119Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P119Expected]

end ConnesWeilRH.Dev
