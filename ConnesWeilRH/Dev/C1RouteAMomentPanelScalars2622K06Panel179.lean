import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P179 : ℚ := ((-19525113 : ℚ) / 132650)

def momentPanelGrowth2622K06P179 : ℚ := ((135361 : ℚ) / 9025)

theorem momentPanelPhase_owner2622K06P179 :
    (momentPanelPhase2622K06P179 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (179 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P179, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P179 :
    (momentPanelGrowth2622K06P179 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (179 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P179, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P179Input : RatPair2542 := (momentPanelPhase2622K06P179 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P179Expected : RatState2542 :=
  ((((31734147465214404652545642261143 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P179_replay :
    compactExp2620 momentScalarAmp2622K06P179Input 20 = momentScalarAmp2622K06P179Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P179_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (179 / 200) 0) -
      (momentScalarAmp2622K06P179Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P179Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P179 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P179]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P179 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P179 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P179Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P179Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P179_replay] at h
  simpa only [momentPanelPhase_owner2622K06P179] using h

theorem momentScalarAmp2622K06P179_radius_le :
    (momentScalarAmp2622K06P179Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P179Expected]

def momentScalarGrow2622K06P179Input : RatPair2542 := (momentPanelGrowth2622K06P179 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P179Expected : RatState2542 :=
  ((((217867356990749143907597337720756987328306459769455165651477208281758394478932954185565636178281455089 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((4418811768227077573367780222600460831338443307233266671 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K06P179_replay :
    compactExp2620 momentScalarGrow2622K06P179Input 20 = momentScalarGrow2622K06P179Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P179_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (179 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P179Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P179Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P179 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P179]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P179 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P179 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P179Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P179Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P179_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P179] using h

theorem momentScalarGrow2622K06P179_radius_le :
    (momentScalarGrow2622K06P179Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 65 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P179Expected]

end ConnesWeilRH.Dev
