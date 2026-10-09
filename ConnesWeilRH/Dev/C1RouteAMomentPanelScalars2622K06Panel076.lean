import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P076 : ℚ := ((-61060317 : ℚ) / 1963550)

def momentPanelGrowth2622K06P076 : ℚ := ((6377467 : ℚ) / 50061675)

theorem momentPanelPhase_owner2622K06P076 :
    (momentPanelPhase2622K06P076 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-27 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P076, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P076 :
    (momentPanelGrowth2622K06P076 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-27 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P076, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P076Input : RatPair2542 := (momentPanelPhase2622K06P076 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P076Expected : RatState2542 :=
  ((((33370042716190843035262705237977542946358451197728655644153078087255546764999402531 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((42302809206835883271516211357259379 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K06P076_replay :
    compactExp2620 momentScalarAmp2622K06P076Input 20 = momentScalarAmp2622K06P076Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P076_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-27 / 200) 0) -
      (momentScalarAmp2622K06P076Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P076Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P076 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P076]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P076 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P076 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P076Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P076Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P076_replay] at h
  simpa only [momentPanelPhase_owner2622K06P076] using h

theorem momentScalarAmp2622K06P076_radius_le :
    (momentScalarAmp2622K06P076Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P076Expected]

def momentScalarGrow2622K06P076Input : RatPair2542 := (momentPanelGrowth2622K06P076 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P076Expected : RatState2542 :=
  ((((37909178103714039019770795645868736935162506501608121613044671079048584301831844473522511122299 : ℚ) / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384), 0), ((3075557538497673627635054540839354634161436940529 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P076_replay :
    compactExp2620 momentScalarGrow2622K06P076Input 20 = momentScalarGrow2622K06P076Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P076_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-27 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P076Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P076Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P076 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P076]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P076 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P076 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P076Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P076Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P076_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P076] using h

theorem momentScalarGrow2622K06P076_radius_le :
    (momentScalarGrow2622K06P076Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P076Expected]

end ConnesWeilRH.Dev
