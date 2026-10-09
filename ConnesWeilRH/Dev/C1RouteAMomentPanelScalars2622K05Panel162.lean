import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P162 : ℚ := ((-6385369298265272744635374668294950007 : ℚ) / 102628992594477452345173091507240960)

def momentPanelGrowth2622K05P162 : ℚ := ((14910241243652276923576036817671329601483 : ℚ) / 7375441679886443756037554997430950297600)

theorem momentPanelPhase_owner2622K05P162 :
    (momentPanelPhase2622K05P162 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (29 / 40) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P162, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P162 :
    (momentPanelGrowth2622K05P162 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (29 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P162, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P162Input : RatPair2542 := (momentPanelPhase2622K05P162 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P162Expected : RatState2542 :=
  ((((1017748121504796503200912717297321337441954736639788289244233238163503 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1210216045185971509490105 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P162_replay :
    compactExp2620 momentScalarAmp2622K05P162Input 20 = momentScalarAmp2622K05P162Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P162_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (29 / 40) 0) -
      (momentScalarAmp2622K05P162Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P162Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P162 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P162]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P162 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P162 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P162Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P162Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P162_replay] at h
  simpa only [momentPanelPhase_owner2622K05P162] using h

theorem momentScalarAmp2622K05P162_radius_le :
    (momentScalarAmp2622K05P162Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P162Expected]

def momentScalarGrow2622K05P162Input : RatPair2542 := (momentPanelGrowth2622K05P162 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P162Expected : RatState2542 :=
  ((((16127653486161960191126638222632436322367163809917567128184509221911993014315842531161231760548981 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((10222095103252366299313308916756863138851903595883 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P162_replay :
    compactExp2620 momentScalarGrow2622K05P162Input 20 = momentScalarGrow2622K05P162Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P162_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (29 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P162Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P162Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P162 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P162]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P162 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P162 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P162Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P162Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P162_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P162] using h

theorem momentScalarGrow2622K05P162_radius_le :
    (momentScalarGrow2622K05P162Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P162Expected]

end ConnesWeilRH.Dev
