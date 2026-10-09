import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P100 : ℚ := ((-94634861609926757210131861186961560575 : ℚ) / 3209407366043425721203717254494027776)

def momentPanelGrowth2622K07P100 : ℚ := ((195784760396604069318440590474900048025 : ℚ) / 1319636322588891376050299861463679893504)

theorem momentPanelPhase_owner2622K07P100 :
    (momentPanelPhase2622K07P100 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (21 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P100, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P100 :
    (momentPanelGrowth2622K07P100 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (21 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P100, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P100Input : RatPair2542 := (momentPanelPhase2622K07P100 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P100Expected : RatState2542 :=
  ((((83487900381641663320208708597282240608998376215457808338130603163934146621442592131 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((423345852746371818934163071915374391 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P100_replay :
    compactExp2620 momentScalarAmp2622K07P100Input 20 = momentScalarAmp2622K07P100Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P100_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (21 / 200) 0) -
      (momentScalarAmp2622K07P100Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P100Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P100 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P100]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P100 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P100 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P100Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P100Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P100_replay] at h
  simpa only [momentPanelPhase_owner2622K07P100] using h

theorem momentScalarAmp2622K07P100_radius_le :
    (momentScalarAmp2622K07P100Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P100Expected]

def momentScalarGrow2622K07P100Input : RatPair2542 := (momentPanelGrowth2622K07P100 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P100Expected : RatState2542 :=
  ((((2477602889198898385424704828379907359272135659821939511573759290919333779364611382128788497460711 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1570367172619352939158188038201995506139320206957 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K07P100_replay :
    compactExp2620 momentScalarGrow2622K07P100Input 20 = momentScalarGrow2622K07P100Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P100_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (21 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P100Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P100Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P100 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P100]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P100 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P100 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P100Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P100Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P100_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P100] using h

theorem momentScalarGrow2622K07P100_radius_le :
    (momentScalarGrow2622K07P100Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P100Expected]

end ConnesWeilRH.Dev
