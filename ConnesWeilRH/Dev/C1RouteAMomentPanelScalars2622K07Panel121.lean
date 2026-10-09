import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P121 : ℚ := ((-89921376401674152003532416315637335525 : ℚ) / 2923182001716693348180973644345769984)

def momentPanelGrowth2622K07P121 : ℚ := ((1357695231916624500793675526178610025 : ℚ) / 4255533488580571578330068581324161024)

theorem momentPanelPhase_owner2622K07P121 :
    (momentPanelPhase2622K07P121 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (63 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P121, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P121 :
    (momentPanelGrowth2622K07P121 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (63 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P121, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P121Input : RatPair2542 := (momentPanelPhase2622K07P121 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P121Expected : RatState2542 :=
  ((((93338710115557841904978204694925704768903757636664343014951075447524643113519828111 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3697635720848029356795345208162595 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarAmp2622K07P121_replay :
    compactExp2620 momentScalarAmp2622K07P121Input 20 = momentScalarAmp2622K07P121Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P121_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (63 / 200) 0) -
      (momentScalarAmp2622K07P121Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P121Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P121 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P121]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P121 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P121 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P121Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P121Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P121_replay] at h
  simpa only [momentPanelPhase_owner2622K07P121] using h

theorem momentScalarAmp2622K07P121_radius_le :
    (momentScalarAmp2622K07P121Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P121Expected]

def momentScalarGrow2622K07P121Input : RatPair2542 := (momentPanelGrowth2622K07P121 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P121Expected : RatState2542 :=
  ((((734677831781694993689790139086608647470829141032812284253006240874656728376592741296427694431479 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3725258044273423898881157828380491488959614027807 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P121_replay :
    compactExp2620 momentScalarGrow2622K07P121Input 20 = momentScalarGrow2622K07P121Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P121_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (63 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P121Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P121Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P121 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P121]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P121 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P121 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P121Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P121Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P121_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P121] using h

theorem momentScalarGrow2622K07P121_radius_le :
    (momentScalarGrow2622K07P121Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P121Expected]

end ConnesWeilRH.Dev
