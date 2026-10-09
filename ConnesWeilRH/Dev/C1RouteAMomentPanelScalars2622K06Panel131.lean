import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P131 : ℚ := ((-19083929 : ℚ) / 551850)

def momentPanelGrowth2622K06P131 : ℚ := ((43614481 : ℚ) / 105987025)

theorem momentPanelPhase_owner2622K06P131 :
    (momentPanelPhase2622K06P131 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (83 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P131, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P131 :
    (momentPanelGrowth2622K06P131 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (83 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P131, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P131Input : RatPair2542 := (momentPanelPhase2622K06P131 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P131Expected : RatState2542 :=
  ((((2046176422582583302269998570125905910325042345358874555866559317255843457372547599 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2593922318072514255763350197448621 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P131_replay :
    compactExp2620 momentScalarAmp2622K06P131Input 20 = momentScalarAmp2622K06P131Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P131_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (83 / 200) 0) -
      (momentScalarAmp2622K06P131Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P131Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P131 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P131]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P131 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P131 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P131Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P131Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P131_replay] at h
  simpa only [momentPanelPhase_owner2622K06P131] using h

theorem momentScalarAmp2622K06P131_radius_le :
    (momentScalarAmp2622K06P131Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P131Expected]

def momentScalarGrow2622K06P131Input : RatPair2542 := (momentPanelGrowth2622K06P131 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P131Expected : RatState2542 :=
  ((((1611699818601046661374860596385246772074748124513661053186042182662831994325643247595446187247551 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1021535720322660469027495915934971613697758661115 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K06P131_replay :
    compactExp2620 momentScalarGrow2622K06P131Input 20 = momentScalarGrow2622K06P131Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P131_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (83 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P131Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P131Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P131 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P131]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P131 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P131 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P131Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P131Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P131_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P131] using h

theorem momentScalarGrow2622K06P131_radius_le :
    (momentScalarGrow2622K06P131Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P131Expected]

end ConnesWeilRH.Dev
