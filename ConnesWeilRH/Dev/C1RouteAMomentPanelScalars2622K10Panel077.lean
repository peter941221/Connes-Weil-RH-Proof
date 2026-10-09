import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K10
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K10P077 : ℚ := ((-52252809243286701296962945029873709 : ℚ) / 1703722406706740315611569108025344)

def momentPanelGrowth2622K10P077 : ℚ := ((3142723168300780710401272176870186028003 : ℚ) / 32671095030091904862012696278314097049600)

theorem momentPanelPhase_owner2622K10P077 :
    (momentPanelPhase2622K10P077 : ℝ) = momentPhase2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (-1 / 8) 0 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelPhase2622K10P077, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K10P077 :
    (momentPanelGrowth2622K10P077 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2))
      (-1 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelGrowth2622K10P077, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K10P077Input : RatPair2542 := (momentPanelPhase2622K10P077 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K10P077Expected : RatState2542 :=
  ((((102300521477291781033900605834493682396153428336244035887851819901372085512614501625 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((8105319409999201196572515297619007 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K10P077_replay :
    compactExp2620 momentScalarAmp2622K10P077Input 20 = momentScalarAmp2622K10P077Expected := by
  decide +kernel

theorem momentScalarAmp2622K10P077_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (-1 / 8) 0) -
      (momentScalarAmp2622K10P077Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K10P077Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K10P077 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelPhase2622K10P077]
  have h := compactExp_real_error2620 momentPanelPhase2622K10P077 20 hsmall
  change |Real.exp (momentPanelPhase2622K10P077 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K10P077Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K10P077Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K10P077_replay] at h
  simpa only [momentPanelPhase_owner2622K10P077] using h

theorem momentScalarAmp2622K10P077_radius_le :
    (momentScalarAmp2622K10P077Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentScalarAmp2622K10P077Expected]

def momentScalarGrow2622K10P077Input : RatPair2542 := (momentPanelGrowth2622K10P077 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K10P077Expected : RatState2542 :=
  ((((1175830189504310846506725793487524721683333216462342364004111790243269581950191027404893780012957 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2981083417508828857545353244037310230952106056441 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K10P077_replay :
    compactExp2620 momentScalarGrow2622K10P077Input 20 = momentScalarGrow2622K10P077Expected := by
  decide +kernel

theorem momentScalarGrow2622K10P077_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 10).re * (storedWidth 10 ^ 2)) (-1 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K10P077Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K10P077Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K10P077 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentPanelGrowth2622K10P077]
  have h := compactExp_real_error2620 momentPanelGrowth2622K10P077 20 hsmall
  change |Real.exp (momentPanelGrowth2622K10P077 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K10P077Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K10P077Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K10P077_replay] at h
  simpa only [momentPanelGrowth_owner2622K10P077] using h

theorem momentScalarGrow2622K10P077_radius_le :
    (momentScalarGrow2622K10P077Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, momentScalarGrow2622K10P077Expected]

end ConnesWeilRH.Dev
