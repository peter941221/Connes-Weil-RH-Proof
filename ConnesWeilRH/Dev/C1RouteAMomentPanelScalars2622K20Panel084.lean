import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K20
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K20P084 : ℚ := ((-813593064647292070314064578280055351287 : ℚ) / 26961407086134165494553081134501068800)

def momentPanelGrowth2622K20P084 : ℚ := ((325638441355425111781964718814354239889 : ℚ) / 6292699723291825538294851697854172364800)

theorem momentPanelPhase_owner2622K20P084 :
    (momentPanelPhase2622K20P084 : ℝ) = momentPhase2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (-11 / 200) 0 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelPhase2622K20P084, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K20P084 :
    (momentPanelGrowth2622K20P084 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2))
      (-11 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelGrowth2622K20P084, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K20P084Input : RatPair2542 := (momentPanelPhase2622K20P084 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K20P084Expected : RatState2542 :=
  ((((41896468269133716758980343971646668606225198855881485554479657707857437405724551343 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((212446446352118208613127909995101947 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K20P084_replay :
    compactExp2620 momentScalarAmp2622K20P084Input 20 = momentScalarAmp2622K20P084Expected := by
  decide +kernel

theorem momentScalarAmp2622K20P084_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (-11 / 200) 0) -
      (momentScalarAmp2622K20P084Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K20P084Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K20P084 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelPhase2622K20P084]
  have h := compactExp_real_error2620 momentPanelPhase2622K20P084 20 hsmall
  change |Real.exp (momentPanelPhase2622K20P084 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K20P084Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K20P084Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K20P084_replay] at h
  simpa only [momentPanelPhase_owner2622K20P084] using h

theorem momentScalarAmp2622K20P084_radius_le :
    (momentScalarAmp2622K20P084Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentScalarAmp2622K20P084Expected]

def momentScalarGrow2622K20P084Input : RatPair2542 := (momentPanelGrowth2622K20P084 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K20P084Expected : RatState2542 :=
  ((((2249431366291275183814089438231541443682369221271109113892824176594151883415339147198459830071147 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((712873220231602255857292206922053503409656826271 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K20P084_replay :
    compactExp2620 momentScalarGrow2622K20P084Input 20 = momentScalarGrow2622K20P084Expected := by
  decide +kernel

theorem momentScalarGrow2622K20P084_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 20).re * (storedWidth 20 ^ 2)) (-11 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K20P084Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K20P084Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K20P084 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentPanelGrowth2622K20P084]
  have h := compactExp_real_error2620 momentPanelGrowth2622K20P084 20 hsmall
  change |Real.exp (momentPanelGrowth2622K20P084 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K20P084Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K20P084Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K20P084_replay] at h
  simpa only [momentPanelGrowth_owner2622K20P084] using h

theorem momentScalarGrow2622K20P084_radius_le :
    (momentScalarGrow2622K20P084Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, momentScalarGrow2622K20P084Expected]

end ConnesWeilRH.Dev
