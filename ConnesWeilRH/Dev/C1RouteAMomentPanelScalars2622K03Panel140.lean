import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P140 : ℚ := ((-72803800607668690926799067013305102982671424033521975 : ℚ) / 1814636970450982335814650180421354904280297243672576)

def momentPanelGrowth2622K03P140 : ℚ := ((2809925368765408998475181706477435142853001845392798425 : ℚ) / 5000637556094336485534205319231518117746936119228891136)

theorem momentPanelPhase_owner2622K03P140 :
    (momentPanelPhase2622K03P140 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (101 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P140, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P140 :
    (momentPanelGrowth2622K03P140 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (101 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P140, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P140Input : RatPair2542 := (momentPanelPhase2622K03P140 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P140Expected : RatState2542 :=
  ((((4022895002885220207712306623561527294629777568281934819893935867585124838426319 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((10199643196215641410284166806379 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P140_replay :
    compactExp2620 momentScalarAmp2622K03P140Input 20 = momentScalarAmp2622K03P140Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P140_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (101 / 200) 0) -
      (momentScalarAmp2622K03P140Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P140Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P140 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P140]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P140 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P140 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P140Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P140Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P140_replay] at h
  simpa only [momentPanelPhase_owner2622K03P140] using h

theorem momentScalarAmp2622K03P140_radius_le :
    (momentScalarAmp2622K03P140Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P140Expected]

def momentScalarGrow2622K03P140Input : RatPair2542 := (momentPanelGrowth2622K03P140 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P140Expected : RatState2542 :=
  ((((1873287848311066252403292332619417165839726045260576460598041740524457432672337600008898621971107 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2374673192765860750971965581713778279130102493091 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P140_replay :
    compactExp2620 momentScalarGrow2622K03P140Input 20 = momentScalarGrow2622K03P140Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P140_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (101 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P140Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P140Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P140 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P140]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P140 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P140 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P140Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P140Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P140_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P140] using h

theorem momentScalarGrow2622K03P140_radius_le :
    (momentScalarGrow2622K03P140Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P140Expected]

end ConnesWeilRH.Dev
