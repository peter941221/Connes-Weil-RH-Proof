import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P140 : ℚ := ((-796938847599586779286070718577339859263 : ℚ) / 20146517459307204232106804702399692800)

def momentPanelGrowth2622K05P140 : ℚ := ((31815559948655315569469870628164660663889 : ℚ) / 55518229525812051567237374252522720460800)

theorem momentPanelPhase_owner2622K05P140 :
    (momentPanelPhase2622K05P140 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (101 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P140, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P140 :
    (momentPanelGrowth2622K05P140 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (101 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P140, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P140Input : RatPair2542 := (momentPanelPhase2622K05P140 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P140Expected : RatState2542 :=
  ((((7065060881361927130047548172187264239949133970609814393270245622377781891933245 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((17912735490320159193040837307627 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P140_replay :
    compactExp2620 momentScalarAmp2622K05P140Input 20 = momentScalarAmp2622K05P140Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P140_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (101 / 200) 0) -
      (momentScalarAmp2622K05P140Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P140Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P140 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P140]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P140 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P140 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P140Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P140Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P140_replay] at h
  simpa only [momentPanelPhase_owner2622K05P140] using h

theorem momentScalarAmp2622K05P140_radius_le :
    (momentScalarAmp2622K05P140Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P140Expected]

def momentScalarGrow2622K05P140Input : RatPair2542 := (momentPanelGrowth2622K05P140 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P140Expected : RatState2542 :=
  ((((3788590140293574641412079972434044168018432246708897603556984956521560458537943175339315352072689 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2401302970326566271099780690913701189728925427545 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P140_replay :
    compactExp2620 momentScalarGrow2622K05P140Input 20 = momentScalarGrow2622K05P140Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P140_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (101 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P140Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P140Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P140 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P140]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P140 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P140 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P140Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P140Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P140_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P140] using h

theorem momentScalarGrow2622K05P140_radius_le :
    (momentScalarGrow2622K05P140Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P140Expected]

end ConnesWeilRH.Dev
