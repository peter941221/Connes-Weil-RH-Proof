import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K14
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K14P012 : ℚ := ((-6594082400043173600043008669327651507 : ℚ) / 86403064911556116006015290478428160)

def momentPanelGrowth2622K14P012 : ℚ := ((2981356347869064514102213485086354629729 : ℚ) / 971974647146675532639921373491023052800)

theorem momentPanelPhase_owner2622K14P012 :
    (momentPanelPhase2622K14P012 : ℝ) = momentPhase2619 ((capturedNodes2584 14).re * (storedWidth 14 ^ 2)) (-31 / 40) 0 := by
  norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentPanelPhase2622K14P012, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K14P012 :
    (momentPanelGrowth2622K14P012 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 14).re * (storedWidth 14 ^ 2))
      (-31 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentPanelGrowth2622K14P012, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K14P012Input : RatPair2542 := (momentPanelPhase2622K14P012 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K14P012Expected : RatState2542 :=
  ((((1531957039064091536453684347969893123879510660093749931082236953 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((302231455146423260778521 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K14P012_replay :
    compactExp2620 momentScalarAmp2622K14P012Input 20 = momentScalarAmp2622K14P012Expected := by
  decide +kernel

theorem momentScalarAmp2622K14P012_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 14).re * (storedWidth 14 ^ 2)) (-31 / 40) 0) -
      (momentScalarAmp2622K14P012Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K14P012Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K14P012 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentPanelPhase2622K14P012]
  have h := compactExp_real_error2620 momentPanelPhase2622K14P012 20 hsmall
  change |Real.exp (momentPanelPhase2622K14P012 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K14P012Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K14P012Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K14P012_replay] at h
  simpa only [momentPanelPhase_owner2622K14P012] using h

theorem momentScalarAmp2622K14P012_radius_le :
    (momentScalarAmp2622K14P012Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentScalarAmp2622K14P012Expected]

def momentScalarGrow2622K14P012Input : RatPair2542 := (momentPanelGrowth2622K14P012 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K14P012Expected : RatState2542 :=
  ((((22945015368731237109241161359221367051406572949175218339499895733801240197367923501232353026204877 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((58172354841453999861835257184954277197533207796043 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K14P012_replay :
    compactExp2620 momentScalarGrow2622K14P012Input 20 = momentScalarGrow2622K14P012Expected := by
  decide +kernel

theorem momentScalarGrow2622K14P012_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 14).re * (storedWidth 14 ^ 2)) (-31 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K14P012Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K14P012Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K14P012 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentPanelGrowth2622K14P012]
  have h := compactExp_real_error2620 momentPanelGrowth2622K14P012 20 hsmall
  change |Real.exp (momentPanelGrowth2622K14P012 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K14P012Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K14P012Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K14P012_replay] at h
  simpa only [momentPanelGrowth_owner2622K14P012] using h

theorem momentScalarGrow2622K14P012_radius_le :
    (momentScalarGrow2622K14P012Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, momentScalarGrow2622K14P012Expected]

end ConnesWeilRH.Dev
