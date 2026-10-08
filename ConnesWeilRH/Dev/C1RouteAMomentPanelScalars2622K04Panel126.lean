import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P126 : ℚ := ((-102776921061459391313311369125113880296411291103732653 : ℚ) / 3298940316920555669078122189785563058235080546713600)

def momentPanelGrowth2622K04P126 : ℚ := ((1391783503385595063390756977436640613005049064233026949 : ℚ) / 3544053980243876701303226846407059068613776154348748800)

theorem momentPanelPhase_owner2622K04P126 :
    (momentPanelPhase2622K04P126 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (73 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P126, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P126 :
    (momentPanelGrowth2622K04P126 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (73 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P126, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P126Input : RatPair2542 := (momentPanelPhase2622K04P126 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P126Expected : RatState2542 :=
  ((((63002820394700853733701972118989280810356975124205776446587419507578623156993840817 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((79867936034475675171375977533842261 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P126_replay :
    compactExp2620 momentScalarAmp2622K04P126Input 20 = momentScalarAmp2622K04P126Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P126_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (73 / 200) 0) -
      (momentScalarAmp2622K04P126Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P126Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P126 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P126]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P126 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P126 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P126Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P126Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P126_replay] at h
  simpa only [momentPanelPhase_owner2622K04P126] using h

theorem momentScalarAmp2622K04P126_radius_le :
    (momentScalarAmp2622K04P126Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P126Expected]

def momentScalarGrow2622K04P126Input : RatPair2542 := (momentPanelGrowth2622K04P126 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P126Expected : RatState2542 :=
  ((((98855351120680078476972720633715988809790373514387119576568715928203177583556064903889793235511 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((4010047944053792667494180712026013056064295432255 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P126_replay :
    compactExp2620 momentScalarGrow2622K04P126Input 20 = momentScalarGrow2622K04P126Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P126_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (73 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P126Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P126Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P126 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P126]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P126 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P126 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P126Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P126Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P126_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P126] using h

theorem momentScalarGrow2622K04P126_radius_le :
    (momentScalarGrow2622K04P126Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P126Expected]

end ConnesWeilRH.Dev
