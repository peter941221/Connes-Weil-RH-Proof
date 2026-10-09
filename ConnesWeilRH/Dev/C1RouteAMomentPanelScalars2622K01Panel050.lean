import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P050 : ℚ := ((-28604019247934411597908621181905386176199139450585451 : ℚ) / 803040914301008327077444600710758438485752387993600)

def momentPanelGrowth2622K01P050 : ℚ := ((1793826477367304471897968867893820700353727772131 : ℚ) / 5245135270694402562889200937726894626206593843200)

theorem momentPanelPhase_owner2622K01P050 :
    (momentPanelPhase2622K01P050 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-79 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P050, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P050 :
    (momentPanelGrowth2622K01P050 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-79 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P050, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P050Input : RatPair2542 := (momentPanelPhase2622K01P050 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P050Expected : RatState2542 :=
  ((((724753620896350716261080996261331778918896310131455374940581097434125565622502383 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((459382787232387150621911553323373 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K01P050_replay :
    compactExp2620 momentScalarAmp2622K01P050Input 20 = momentScalarAmp2622K01P050Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P050_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-79 / 200) 0) -
      (momentScalarAmp2622K01P050Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P050Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P050 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P050]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P050 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P050 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P050Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P050Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P050_replay] at h
  simpa only [momentPanelPhase_owner2622K01P050] using h

theorem momentScalarAmp2622K01P050_radius_le :
    (momentScalarAmp2622K01P050Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P050Expected]

def momentScalarGrow2622K01P050Input : RatPair2542 := (momentPanelGrowth2622K01P050 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P050Expected : RatState2542 :=
  ((((751738033866151833118359317606604909995453507962363416585662323561528384699531677864001763005111 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3811763436153980561178958887344929727814241041701 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P050_replay :
    compactExp2620 momentScalarGrow2622K01P050Input 20 = momentScalarGrow2622K01P050Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P050_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-79 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P050Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P050Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P050 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P050]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P050 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P050 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P050Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P050Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P050_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P050] using h

theorem momentScalarGrow2622K01P050_radius_le :
    (momentScalarGrow2622K01P050Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P050Expected]

end ConnesWeilRH.Dev
