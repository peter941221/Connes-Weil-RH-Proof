import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P057 : ℚ := ((-2931387244718078393988566993641360041546522361569125 : ℚ) / 87142035125855086497894708150708375046984977874944)

def momentPanelGrowth2622K03P057 : ℚ := ((1830080195692388080088880852254133442652922185204164425 : ℚ) / 7253242722204270498846953733472961554527526668055085056)

theorem momentPanelPhase_owner2622K03P057 :
    (momentPanelPhase2622K03P057 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-13 / 40) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P057, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P057 :
    (momentPanelGrowth2622K03P057 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-13 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P057, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P057Input : RatPair2542 := (momentPanelPhase2622K03P057 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P057Expected : RatState2542 :=
  ((((1312880458132599789325192505166475047019948850160327074988061202236971313039168607 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((6657308374082323624914370283292361 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P057_replay :
    compactExp2620 momentScalarAmp2622K03P057Input 20 = momentScalarAmp2622K03P057Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P057_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-13 / 40) 0) -
      (momentScalarAmp2622K03P057Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P057Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P057 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P057]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P057 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P057 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P057Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P057Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P057_replay] at h
  simpa only [momentPanelPhase_owner2622K03P057] using h

theorem momentScalarAmp2622K03P057_radius_le :
    (momentScalarAmp2622K03P057Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P057Expected]

def momentScalarGrow2622K03P057Input : RatPair2542 := (momentPanelGrowth2622K03P057 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P057Expected : RatState2542 :=
  ((((2749010020255720477683591073973228704635656005375426527615304249146883069979304900387169993372275 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1742391681844896273504439629594025833172153955589 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P057_replay :
    compactExp2620 momentScalarGrow2622K03P057Input 20 = momentScalarGrow2622K03P057Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P057_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-13 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P057Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P057Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P057 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P057]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P057 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P057 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P057Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P057Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P057_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P057] using h

theorem momentScalarGrow2622K03P057_radius_le :
    (momentScalarGrow2622K03P057Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P057Expected]

end ConnesWeilRH.Dev
