import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P085 : ℚ := ((-85658731971150281328726007486523918372812259531716983 : ℚ) / 2848715032256460624598285880722719817463143124172800)

def momentPanelGrowth2622K01P085 : ℚ := ((60615744704270913269946656373564397990291176619291 : ℚ) / 1893493832720679325203001538519408960060580377395200)

theorem momentPanelPhase_owner2622K01P085 :
    (momentPanelPhase2622K01P085 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-9 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P085, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P085 :
    (momentPanelGrowth2622K01P085 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-9 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P085, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P085Input : RatPair2542 := (momentPanelPhase2622K01P085 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P085Expected : RatState2542 :=
  ((((23312998408218761857085873938168517464418656901623034724142168039886319155596775101 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((118214335600468848843921974667514821 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P085_replay :
    compactExp2620 momentScalarAmp2622K01P085Input 20 = momentScalarAmp2622K01P085Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P085_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-9 / 200) 0) -
      (momentScalarAmp2622K01P085Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P085Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P085 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P085]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P085 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P085 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P085Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P085Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P085_replay] at h
  simpa only [momentPanelPhase_owner2622K01P085] using h

theorem momentScalarAmp2622K01P085_radius_le :
    (momentScalarAmp2622K01P085Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P085Expected]

def momentScalarGrow2622K01P085Input : RatPair2542 := (momentPanelGrowth2622K01P085 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P085Expected : RatState2542 :=
  ((((1102735946171723835922741621501580601314736346762852640171552236224528338084311255644128565204105 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2795767682761887345001277645290825142154554052169 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P085_replay :
    compactExp2620 momentScalarGrow2622K01P085Input 20 = momentScalarGrow2622K01P085Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P085_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-9 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P085Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P085Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P085 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P085]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P085 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P085 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P085Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P085Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P085_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P085] using h

theorem momentScalarGrow2622K01P085_radius_le :
    (momentScalarGrow2622K01P085Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P085Expected]

end ConnesWeilRH.Dev
