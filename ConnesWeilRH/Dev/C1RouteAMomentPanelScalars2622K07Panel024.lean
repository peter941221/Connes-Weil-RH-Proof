import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P024 : ℚ := ((-35718063823129739042565287072158715725 : ℚ) / 617639937250400667750041696161759232)

def momentPanelGrowth2622K07P024 : ℚ := ((106918275925667527023990684483895545075 : ℚ) / 80761350421023574664230970955212521472)

theorem momentPanelPhase_owner2622K07P024 :
    (momentPanelPhase2622K07P024 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-131 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P024, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P024 :
    (momentPanelGrowth2622K07P024 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-131 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P024, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P024Input : RatPair2542 := (momentPanelPhase2622K07P024 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P024Expected : RatState2542 :=
  ((((5119605992329302103241118676441328778934780996724474333450990100332359 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((2625538984550794607913127 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P024_replay :
    compactExp2620 momentScalarAmp2622K07P024Input 20 = momentScalarAmp2622K07P024Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P024_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-131 / 200) 0) -
      (momentScalarAmp2622K07P024Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P024Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P024 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P024]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P024 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P024 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P024Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P024Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P024_replay] at h
  simpa only [momentPanelPhase_owner2622K07P024] using h

theorem momentScalarAmp2622K07P024_radius_le :
    (momentScalarAmp2622K07P024Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P024Expected]

def momentScalarGrow2622K07P024Input : RatPair2542 := (momentPanelGrowth2622K07P024 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P024Expected : RatState2542 :=
  ((((4013488928303936971263272087103589577347154098037117827637431193954527071105835320225772877545417 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((317980951593876305734632568067216033472244650731 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarGrow2622K07P024_replay :
    compactExp2620 momentScalarGrow2622K07P024Input 20 = momentScalarGrow2622K07P024Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P024_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-131 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P024Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P024Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P024 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P024]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P024 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P024 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P024Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P024Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P024_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P024] using h

theorem momentScalarGrow2622K07P024_radius_le :
    (momentScalarGrow2622K07P024Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P024Expected]

end ConnesWeilRH.Dev
