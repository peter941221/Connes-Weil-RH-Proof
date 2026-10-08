import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P138 : ℚ := ((-100811050672584510674435405677414330564498367537337557 : ℚ) / 2910728944504534581430268406095300381138973464985600)

def momentPanelGrowth2622K04P138 : ℚ := ((1658861683164980308115459755062715432624059113255362709 : ℚ) / 2747204466433826828189813090231772540029652121210060800)

theorem momentPanelPhase_owner2622K04P138 :
    (momentPanelPhase2622K04P138 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (97 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P138, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P138 :
    (momentPanelGrowth2622K04P138 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (97 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P138, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P138Input : RatPair2542 := (momentPanelPhase2622K04P138 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P138Expected : RatState2542 :=
  ((((121337367878786676945220775403325296790362861768748965871139496146284918014377755 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((1230547743105346921837413981770025 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P138_replay :
    compactExp2620 momentScalarAmp2622K04P138Input 20 = momentScalarAmp2622K04P138Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P138_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (97 / 200) 0) -
      (momentScalarAmp2622K04P138Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P138Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P138 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P138]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P138 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P138 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P138Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P138Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P138_replay] at h
  simpa only [momentPanelPhase_owner2622K04P138] using h

theorem momentScalarAmp2622K04P138_radius_le :
    (momentScalarAmp2622K04P138Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P138Expected]

def momentScalarGrow2622K04P138Input : RatPair2542 := (momentPanelGrowth2622K04P138 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P138Expected : RatState2542 :=
  ((((3906981638328671544558836333302646479264493168195704591753259927576353490401352769784979018249541 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2476342383419302309870473153944268462836851555893 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P138_replay :
    compactExp2620 momentScalarGrow2622K04P138Input 20 = momentScalarGrow2622K04P138Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P138_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (97 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P138Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P138Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P138 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P138]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P138 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P138 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P138Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P138Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P138_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P138] using h

theorem momentScalarGrow2622K04P138_radius_le :
    (momentScalarGrow2622K04P138Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P138Expected]

end ConnesWeilRH.Dev
