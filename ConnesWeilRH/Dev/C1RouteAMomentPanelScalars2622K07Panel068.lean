import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P068 : ℚ := ((-34242749444078418271208654125234098325 : ℚ) / 1031725611718553171125348778417061888)

def momentPanelGrowth2622K07P068 : ℚ := ((17333844514848932787852615070070073025 : ℚ) / 76527437981080495766572830143759253504)

theorem momentPanelPhase_owner2622K07P068 :
    (momentPanelPhase2622K07P068 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-43 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P068, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P068 :
    (momentPanelGrowth2622K07P068 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-43 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P068, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P068Input : RatPair2542 := (momentPanelPhase2622K07P068 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P068Expected : RatState2542 :=
  ((((257222470837997833225862594797115589912445712271306475810472691469957799648022779 : ℚ) / 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768), 0), ((5217256649274831863149224147216767 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P068_replay :
    compactExp2620 momentScalarAmp2622K07P068Input 20 = momentScalarAmp2622K07P068Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P068_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-43 / 200) 0) -
      (momentScalarAmp2622K07P068Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P068Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P068 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P068]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P068 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P068 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P068Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P068Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P068_replay] at h
  simpa only [momentPanelPhase_owner2622K07P068] using h

theorem momentScalarAmp2622K07P068_radius_le :
    (momentScalarAmp2622K07P068Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P068Expected]

def momentScalarGrow2622K07P068Input : RatPair2542 := (momentPanelGrowth2622K07P068 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P068Expected : RatState2542 :=
  ((((669743452740886170404202937256835887860590713111471953938263553199902699010759089575889419098839 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3396002025886491834468005177063665560296960938019 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P068_replay :
    compactExp2620 momentScalarGrow2622K07P068Input 20 = momentScalarGrow2622K07P068Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P068_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-43 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P068Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P068Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P068 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P068]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P068 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P068 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P068Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P068Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P068_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P068] using h

theorem momentScalarGrow2622K07P068_radius_le :
    (momentScalarGrow2622K07P068Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P068Expected]

end ConnesWeilRH.Dev
