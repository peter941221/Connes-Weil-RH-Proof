import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P157 : ℚ := ((-683516393984987776159236483452565420515913613727859 : ℚ) / 12431327403468910564017670793905102637893723095040)

def momentPanelGrowth2622K01P157 : ℚ := ((7414311165684475585538142863797228061157854492131 : ℚ) / 5245135270694402562889200937726894626206593843200)

theorem momentPanelPhase_owner2622K01P157 :
    (momentPanelPhase2622K01P157 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (27 / 40) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P157, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P157 :
    (momentPanelGrowth2622K01P157 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (27 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P157, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P157Input : RatPair2542 := (momentPanelPhase2622K01P157 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P157Expected : RatState2542 :=
  ((((1411205450541496218099906096194104932916012222939587107351017198000166835 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((5995870124989731276753293 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P157_replay :
    compactExp2620 momentScalarAmp2622K01P157Input 20 = momentScalarAmp2622K01P157Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P157_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (27 / 40) 0) -
      (momentScalarAmp2622K01P157Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P157Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P157 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P157]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P157 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P157 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P157Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P157Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P157_replay] at h
  simpa only [momentPanelPhase_owner2622K01P157] using h

theorem momentScalarAmp2622K01P157_radius_le :
    (momentScalarAmp2622K01P157Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 95 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P157Expected]

def momentScalarGrow2622K01P157Input : RatPair2542 := (momentPanelGrowth2622K01P157 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P157Expected : RatState2542 :=
  ((((8780105497634176780528159636421534672982367299673732236301919552631185661451311942771150336607585 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5565045499965252486777936709897178167802696502689 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P157_replay :
    compactExp2620 momentScalarGrow2622K01P157Input 20 = momentScalarGrow2622K01P157Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P157_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (27 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P157Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P157Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P157 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P157]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P157 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P157 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P157Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P157Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P157_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P157] using h

theorem momentScalarGrow2622K01P157_radius_le :
    (momentScalarGrow2622K01P157Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P157Expected]

end ConnesWeilRH.Dev
