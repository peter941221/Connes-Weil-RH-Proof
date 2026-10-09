import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P083 : ℚ := ((-115186981600146321303163296053053854067837019048773079 : ℚ) / 3789913523211405868162172563276189385150745385369600)

def momentPanelGrowth2622K02P083 : ℚ := ((392420771792815631412398093608039062964277528834129093 : ℚ) / 4710983111781811147735529921316721888081400856104140800)

theorem momentPanelPhase_owner2622K02P083 :
    (momentPanelPhase2622K02P083 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-13 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P083, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P083 :
    (momentPanelGrowth2622K02P083 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-13 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P083, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P083Input : RatPair2542 := (momentPanelPhase2622K02P083 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P083Expected : RatState2542 :=
  ((((134918155056457997189570666515527013528782277592944560652003258359213316180450803245 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((171034037601196548689077723341764991 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P083_replay :
    compactExp2620 momentScalarAmp2622K02P083Input 20 = momentScalarAmp2622K02P083Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P083_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-13 / 200) 0) -
      (momentScalarAmp2622K02P083Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P083Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P083 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P083]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P083 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P083 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P083Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P083Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P083_replay] at h
  simpa only [momentPanelPhase_owner2622K02P083] using h

theorem momentScalarAmp2622K02P083_radius_le :
    (momentScalarAmp2622K02P083Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P083Expected]

def momentScalarGrow2622K02P083Input : RatPair2542 := (momentPanelGrowth2622K02P083 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P083Expected : RatState2542 :=
  ((((1160766771128251197569721317327238965566656910077158840667833640853065307761553320708629008684503 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((183930822156705387293770646796020373182996965795 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K02P083_replay :
    compactExp2620 momentScalarGrow2622K02P083Input 20 = momentScalarGrow2622K02P083Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P083_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-13 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P083Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P083Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P083 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P083]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P083 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P083 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P083Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P083Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P083_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P083] using h

theorem momentScalarGrow2622K02P083_radius_le :
    (momentScalarGrow2622K02P083Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P083Expected]

end ConnesWeilRH.Dev
