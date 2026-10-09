import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P179 : ℚ := ((-72946669081893860438419621232618229120541839545317025 : ℚ) / 484670480479860680249296982649537356393398629564416)

def momentPanelGrowth2622K03P179 : ℚ := ((493354419538070700650454233702070454944446859975825 : ℚ) / 32975130692278497091970639038161135630986978000896)

theorem momentPanelPhase_owner2622K03P179 :
    (momentPanelPhase2622K03P179 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (179 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P179, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P179 :
    (momentPanelGrowth2622K03P179 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (179 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P179, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P179Input : RatPair2542 := (momentPanelPhase2622K03P179 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P179Expected : RatState2542 :=
  ((((9223766699669207059820963449641 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P179_replay :
    compactExp2620 momentScalarAmp2622K03P179Input 20 = momentScalarAmp2622K03P179Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P179_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (179 / 200) 0) -
      (momentScalarAmp2622K03P179Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P179Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P179 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P179]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P179 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P179 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P179Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P179Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P179_replay] at h
  simpa only [momentPanelPhase_owner2622K03P179] using h

theorem momentScalarAmp2622K03P179_radius_le :
    (momentScalarAmp2622K03P179Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P179Expected]

def momentScalarGrow2622K03P179Input : RatPair2542 := (momentPanelGrowth2622K03P179 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P179Expected : RatState2542 :=
  ((((3359123868977293193057419789739171814923279372895593477552339277187475294042526064177563480170975830681 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4258134631924952483567947134652613329484879236025892289 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P179_replay :
    compactExp2620 momentScalarGrow2622K03P179Input 20 = momentScalarGrow2622K03P179Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P179_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (179 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P179Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P179Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P179 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P179]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P179 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P179 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P179Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P179Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P179_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P179] using h

theorem momentScalarGrow2622K03P179_radius_le :
    (momentScalarGrow2622K03P179Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 65 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P179Expected]

end ConnesWeilRH.Dev
