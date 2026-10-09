import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P061 : ℚ := ((-104216145419744182660236001047693252525 : ℚ) / 2981595341375210159001941728049496064)

def momentPanelGrowth2622K07P061 : ℚ := ((326854053096300146427643421671977844025 : ℚ) / 1134290795852417535315368131871757041664)

theorem momentPanelPhase_owner2622K07P061 :
    (momentPanelPhase2622K07P061 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-57 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P061, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P061 :
    (momentPanelGrowth2622K07P061 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-57 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P061, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P061Input : RatPair2542 := (momentPanelPhase2622K07P061 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P061Expected : RatState2542 :=
  ((((1411363864510424795107505400612677692895893931752405065845696334712190319864918771 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1789175891657268483695495004792981 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P061_replay :
    compactExp2620 momentScalarAmp2622K07P061Input 20 = momentScalarAmp2622K07P061Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P061_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-57 / 200) 0) -
      (momentScalarAmp2622K07P061Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P061Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P061 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P061]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P061 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P061 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P061Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P061Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P061_replay] at h
  simpa only [momentPanelPhase_owner2622K07P061] using h

theorem momentScalarAmp2622K07P061_radius_le :
    (momentScalarAmp2622K07P061Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P061Expected]

def momentScalarGrow2622K07P061Input : RatPair2542 := (momentPanelGrowth2622K07P061 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P061Expected : RatState2542 :=
  ((((1424668087241037846164992139859708637915604897131285686435455936995154083900530621928213247551679 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((225747607452355113654039313829940740659452521521 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K07P061_replay :
    compactExp2620 momentScalarGrow2622K07P061Input 20 = momentScalarGrow2622K07P061Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P061_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-57 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P061Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P061Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P061 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P061]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P061 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P061 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P061Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P061Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P061_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P061] using h

theorem momentScalarGrow2622K07P061_radius_le :
    (momentScalarGrow2622K07P061Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P061Expected]

end ConnesWeilRH.Dev
