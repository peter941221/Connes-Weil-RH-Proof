import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P129 : ℚ := ((-28485888460303983644422817596074419279110725509414549 : ℚ) / 803040914301008327077444600710758438485752387993600)

def momentPanelGrowth2622K01P129 : ℚ := ((1793826477367304471897968867893820700353727772131 : ℚ) / 5245135270694402562889200937726894626206593843200)

theorem momentPanelPhase_owner2622K01P129 :
    (momentPanelPhase2622K01P129 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (79 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P129, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P129 :
    (momentPanelGrowth2622K01P129 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (79 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P129, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P129Input : RatPair2542 := (momentPanelPhase2622K01P129 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P129Expected : RatState2542 :=
  ((((839608812408404719518774930406870093885651698184666565268144337332501510930736283 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1064366623524325876109674095828609 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P129_replay :
    compactExp2620 momentScalarAmp2622K01P129Input 20 = momentScalarAmp2622K01P129Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P129_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (79 / 200) 0) -
      (momentScalarAmp2622K01P129Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P129Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P129 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P129]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P129 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P129 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P129Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P129Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P129_replay] at h
  simpa only [momentPanelPhase_owner2622K01P129] using h

theorem momentScalarAmp2622K01P129_radius_le :
    (momentScalarAmp2622K01P129Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P129Expected]

def momentScalarGrow2622K01P129Input : RatPair2542 := (momentPanelGrowth2622K01P129 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P129Expected : RatState2542 :=
  ((((751738033866151833118359317606604909995453507962363416585662323561528384699531677864001763005111 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3811763436153980561178958887344929727814241041701 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P129_replay :
    compactExp2620 momentScalarGrow2622K01P129Input 20 = momentScalarGrow2622K01P129Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P129_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (79 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P129Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P129Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P129 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P129]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P129 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P129 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P129Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P129Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P129_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P129] using h

theorem momentScalarGrow2622K01P129_radius_le :
    (momentScalarGrow2622K01P129Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P129Expected]

end ConnesWeilRH.Dev
