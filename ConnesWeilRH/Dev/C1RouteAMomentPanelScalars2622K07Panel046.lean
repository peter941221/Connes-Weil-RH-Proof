import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P046 : ℚ := ((-106596085140998343387955263501742894275 : ℚ) / 2631115303424109294076133225827139584)

def momentPanelGrowth2622K07P046 : ℚ := ((26120624256600766903881997654937225 : ℚ) / 53667255811262319941764426902798336)

theorem momentPanelPhase_owner2622K07P046 :
    (momentPanelPhase2622K07P046 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-87 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P046, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P046 :
    (momentPanelGrowth2622K07P046 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-87 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P046, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P046Input : RatPair2542 := (momentPanelPhase2622K07P046 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P046Expected : RatState2542 :=
  ((((5429300405076970747632034787539228598671420816059914915339898420098186797033707 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((430170266035461985472458499679 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K07P046_replay :
    compactExp2620 momentScalarAmp2622K07P046Input 20 = momentScalarAmp2622K07P046Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P046_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-87 / 200) 0) -
      (momentScalarAmp2622K07P046Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P046Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P046 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P046]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P046 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P046 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P046Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P046Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P046_replay] at h
  simpa only [momentPanelPhase_owner2622K07P046] using h

theorem momentScalarAmp2622K07P046_radius_le :
    (momentScalarAmp2622K07P046Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P046Expected]

def momentScalarGrow2622K07P046Input : RatPair2542 := (momentPanelGrowth2622K07P046 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P046Expected : RatState2542 :=
  ((((1737584681393462296540502460237715799987429490966169441223717478312436145860931456294165001106217 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4405298483836995666308220247023019859137369549971 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P046_replay :
    compactExp2620 momentScalarGrow2622K07P046Input 20 = momentScalarGrow2622K07P046Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P046_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-87 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P046Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P046Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P046 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P046]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P046 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P046 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P046Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P046Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P046_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P046] using h

theorem momentScalarGrow2622K07P046_radius_le :
    (momentScalarGrow2622K07P046Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P046Expected]

end ConnesWeilRH.Dev
