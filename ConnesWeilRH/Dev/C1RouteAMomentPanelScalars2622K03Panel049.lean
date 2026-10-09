import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P049 : ℚ := ((-219957659002365563268032816960204358250718572811929575 : ℚ) / 6108894156338507835226627140149973486784341038071808)

def momentPanelGrowth2622K03P049 : ℚ := ((755257497296852086500993383393513967284305188886605475 : ℚ) / 2107173604463148859820974205256001322222224370860818432)

theorem momentPanelPhase_owner2622K03P049 :
    (momentPanelPhase2622K03P049 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-81 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P049, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P049 :
    (momentPanelGrowth2622K03P049 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-81 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P049, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P049Input : RatPair2542 := (momentPanelPhase2622K03P049 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P049Expected : RatState2542 :=
  ((((492417507146763825197539960127820966680751664409039716302858775179736525613013621 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((78029348199903153566342803895299 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K03P049_replay :
    compactExp2620 momentScalarAmp2622K03P049Input 20 = momentScalarAmp2622K03P049Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P049_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-81 / 200) 0) -
      (momentScalarAmp2622K03P049Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P049Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P049 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P049]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P049 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P049 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P049Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P049Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P049_replay] at h
  simpa only [momentPanelPhase_owner2622K03P049] using h

theorem momentScalarAmp2622K03P049_radius_le :
    (momentScalarAmp2622K03P049Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P049Expected]

def momentScalarGrow2622K03P049Input : RatPair2542 := (momentPanelGrowth2622K03P049 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P049Expected : RatState2542 :=
  ((((3056745868769891981453644498695237206466919668667589078575269009134382799796294180897688087798105 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3874884410786197101271165648283011393982350211989 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P049_replay :
    compactExp2620 momentScalarGrow2622K03P049Input 20 = momentScalarGrow2622K03P049Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P049_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-81 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P049Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P049Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P049 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P049]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P049 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P049 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P049Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P049Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P049_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P049] using h

theorem momentScalarGrow2622K03P049_radius_le :
    (momentScalarGrow2622K03P049Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P049Expected]

end ConnesWeilRH.Dev
