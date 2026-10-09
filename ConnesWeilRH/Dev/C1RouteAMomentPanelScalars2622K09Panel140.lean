import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K09
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K09P140 : ℚ := ((-795538906394374438875953289886799762023 : ℚ) / 20146517459307204232106804702399692800)

def momentPanelGrowth2622K09P140 : ℚ := ((31891953032482833028955654157281809344169 : ℚ) / 55518229525812051567237374252522720460800)

theorem momentPanelPhase_owner2622K09P140 :
    (momentPanelPhase2622K09P140 : ℝ) = momentPhase2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (101 / 200) 0 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelPhase2622K09P140, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K09P140 :
    (momentPanelGrowth2622K09P140 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2))
      (101 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelGrowth2622K09P140, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K09P140Input : RatPair2542 := (momentPanelPhase2622K09P140 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K09P140Expected : RatState2542 :=
  ((((7573456993501527810942152099951591800396061017997681576131811746787221397820305 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((9600860058434623788822720710533 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K09P140_replay :
    compactExp2620 momentScalarAmp2622K09P140Input 20 = momentScalarAmp2622K09P140Expected := by
  decide +kernel

theorem momentScalarAmp2622K09P140_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (101 / 200) 0) -
      (momentScalarAmp2622K09P140Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K09P140Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K09P140 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelPhase2622K09P140]
  have h := compactExp_real_error2620 momentPanelPhase2622K09P140 20 hsmall
  change |Real.exp (momentPanelPhase2622K09P140 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K09P140Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K09P140Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K09P140_replay] at h
  simpa only [momentPanelPhase_owner2622K09P140] using h

theorem momentScalarAmp2622K09P140_radius_le :
    (momentScalarAmp2622K09P140Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentScalarAmp2622K09P140Expected]

def momentScalarGrow2622K09P140Input : RatPair2542 := (momentPanelGrowth2622K09P140 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K09P140Expected : RatState2542 :=
  ((((1896903414292533571972076527923901225636847756864107560275363604694788444660839619984681770410969 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4809218868772035759096176413003708967556826428309 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K09P140_replay :
    compactExp2620 momentScalarGrow2622K09P140Input 20 = momentScalarGrow2622K09P140Expected := by
  decide +kernel

theorem momentScalarGrow2622K09P140_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (101 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K09P140Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K09P140Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K09P140 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelGrowth2622K09P140]
  have h := compactExp_real_error2620 momentPanelGrowth2622K09P140 20 hsmall
  change |Real.exp (momentPanelGrowth2622K09P140 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K09P140Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K09P140Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K09P140_replay] at h
  simpa only [momentPanelGrowth_owner2622K09P140] using h

theorem momentScalarGrow2622K09P140_radius_le :
    (momentScalarGrow2622K09P140Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentScalarGrow2622K09P140Expected]

end ConnesWeilRH.Dev
