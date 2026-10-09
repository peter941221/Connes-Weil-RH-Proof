import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P055 : ℚ := ((-105318799405777753853525343353324607825 : ℚ) / 2858927328092324856277908752271671296)

def momentPanelGrowth2622K07P055 : ℚ := ((588822093869467839003865828936740425 : ℚ) / 1665875430386326298600483537125638144)

theorem momentPanelPhase_owner2622K07P055 :
    (momentPanelPhase2622K07P055 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-69 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P055, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P055 :
    (momentPanelGrowth2622K07P055 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-69 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P055, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P055Input : RatPair2542 := (momentPanelPhase2622K07P055 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P055Expected : RatState2542 :=
  ((((214195427302355058894826759010260165061535433573195448588063253675236174728385781 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((271534503786274543296813922265689 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P055_replay :
    compactExp2620 momentScalarAmp2622K07P055Input 20 = momentScalarAmp2622K07P055Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P055_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-69 / 200) 0) -
      (momentScalarAmp2622K07P055Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P055Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P055 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P055]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P055 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P055 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P055Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P055Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P055_replay] at h
  simpa only [momentPanelPhase_owner2622K07P055] using h

theorem momentScalarAmp2622K07P055_radius_le :
    (momentScalarAmp2622K07P055Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P055Expected]

def momentScalarGrow2622K07P055Input : RatPair2542 := (momentPanelGrowth2622K07P055 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P055Expected : RatState2542 :=
  ((((1520809456442777033850727169770894349527610666286297575397277698180440551867899926211068840454789 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((120490898152388188289209740629917876046045226333 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarGrow2622K07P055_replay :
    compactExp2620 momentScalarGrow2622K07P055Input 20 = momentScalarGrow2622K07P055Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P055_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-69 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P055Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P055Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P055 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P055]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P055 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P055 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P055Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P055Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P055_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P055] using h

theorem momentScalarGrow2622K07P055_radius_le :
    (momentScalarGrow2622K07P055Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P055Expected]

end ConnesWeilRH.Dev
