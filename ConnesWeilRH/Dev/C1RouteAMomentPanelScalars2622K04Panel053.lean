import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P053 : ℚ := ((-125582709771494189656014385986805341524828168736267347 : ℚ) / 3298940316920555669078122189785563058235080546713600)

def momentPanelGrowth2622K04P053 : ℚ := ((1391783503385595063390756977436640613005049064233026949 : ℚ) / 3544053980243876701303226846407059068613776154348748800)

theorem momentPanelPhase_owner2622K04P053 :
    (momentPanelPhase2622K04P053 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-73 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P053, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P053 :
    (momentPanelGrowth2622K04P053 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-73 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P053, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P053Input : RatPair2542 := (momentPanelPhase2622K04P053 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P053Expected : RatState2542 :=
  ((((62669182055604174105893314705893288898538860173138402633298113099573512401498835 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((39722756405272036671859494468981 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P053_replay :
    compactExp2620 momentScalarAmp2622K04P053Input 20 = momentScalarAmp2622K04P053Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P053_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-73 / 200) 0) -
      (momentScalarAmp2622K04P053Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P053Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P053 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P053]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P053 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P053 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P053Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P053Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P053_replay] at h
  simpa only [momentPanelPhase_owner2622K04P053] using h

theorem momentScalarAmp2622K04P053_radius_le :
    (momentScalarAmp2622K04P053Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P053Expected]

def momentScalarGrow2622K04P053Input : RatPair2542 := (momentPanelGrowth2622K04P053 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P053Expected : RatState2542 :=
  ((((98855351120680078476972720633715988809790373514387119576568715928203177583556064903889793235511 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((4010047944053792667494180712026013056064295432255 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P053_replay :
    compactExp2620 momentScalarGrow2622K04P053Input 20 = momentScalarGrow2622K04P053Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P053_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-73 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P053Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P053Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P053 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P053]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P053 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P053 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P053Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P053Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P053_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P053] using h

theorem momentScalarGrow2622K04P053_radius_le :
    (momentScalarGrow2622K04P053Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P053Expected]

end ConnesWeilRH.Dev
