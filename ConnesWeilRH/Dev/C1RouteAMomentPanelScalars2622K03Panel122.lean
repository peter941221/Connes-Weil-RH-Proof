import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P122 : ℚ := ((-2914619304605533278826172337223772037077207810334875 : ℚ) / 87142035125855086497894708150708375046984977874944)

def momentPanelGrowth2622K03P122 : ℚ := ((1830080195692388080088880852254133442652922185204164425 : ℚ) / 7253242722204270498846953733472961554527526668055085056)

theorem momentPanelPhase_owner2622K03P122 :
    (momentPanelPhase2622K03P122 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (13 / 40) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P122, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P122 :
    (momentPanelGrowth2622K03P122 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (13 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P122, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P122Input : RatPair2542 := (momentPanelPhase2622K03P122 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P122Expected : RatState2542 :=
  ((((6365792335564593965371063807541155673421973182423151907603025722289356911070515997 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((8069857880276282347903721585394411 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P122_replay :
    compactExp2620 momentScalarAmp2622K03P122Input 20 = momentScalarAmp2622K03P122Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P122_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (13 / 40) 0) -
      (momentScalarAmp2622K03P122Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P122Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P122 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P122]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P122 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P122 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P122Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P122Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P122_replay] at h
  simpa only [momentPanelPhase_owner2622K03P122] using h

theorem momentScalarAmp2622K03P122_radius_le :
    (momentScalarAmp2622K03P122Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P122Expected]

def momentScalarGrow2622K03P122Input : RatPair2542 := (momentPanelGrowth2622K03P122 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P122Expected : RatState2542 :=
  ((((2749010020255720477683591073973228704635656005375426527615304249146883069979304900387169993372275 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1742391681844896273504439629594025833172153955589 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P122_replay :
    compactExp2620 momentScalarGrow2622K03P122Input 20 = momentScalarGrow2622K03P122Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P122_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (13 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P122Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P122Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P122 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P122]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P122 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P122 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P122Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P122Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P122_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P122] using h

theorem momentScalarGrow2622K03P122_radius_le :
    (momentScalarGrow2622K03P122Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P122Expected]

end ConnesWeilRH.Dev
