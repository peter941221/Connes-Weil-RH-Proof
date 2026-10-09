import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K18
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K18P034 : ℚ := ((-2482145924456753827761414044483438389161 : ℚ) / 56139681541947458566443596834563686400)

def momentPanelGrowth2622K18P034 : ℚ := ((45331329810014150918583764838684292043 : ℚ) / 62213249097760951274894601232161177600)

theorem momentPanelPhase_owner2622K18P034 :
    (momentPanelPhase2622K18P034 : ℝ) = momentPhase2619 ((capturedNodes2584 18).re * (storedWidth 18 ^ 2)) (-111 / 200) 0 := by
  norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentPanelPhase2622K18P034, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K18P034 :
    (momentPanelGrowth2622K18P034 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 18).re * (storedWidth 18 ^ 2))
      (-111 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentPanelGrowth2622K18P034, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K18P034Input : RatPair2542 := (momentPanelPhase2622K18P034 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K18P034Expected : RatState2542 :=
  ((((33554467840569584827082097741712799466321881881881061861749893645807670564559 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((170150957295633880718156160733 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K18P034_replay :
    compactExp2620 momentScalarAmp2622K18P034Input 20 = momentScalarAmp2622K18P034Expected := by
  decide +kernel

theorem momentScalarAmp2622K18P034_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 18).re * (storedWidth 18 ^ 2)) (-111 / 200) 0) -
      (momentScalarAmp2622K18P034Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K18P034Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K18P034 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentPanelPhase2622K18P034]
  have h := compactExp_real_error2620 momentPanelPhase2622K18P034 20 hsmall
  change |Real.exp (momentPanelPhase2622K18P034 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K18P034Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K18P034Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K18P034_replay] at h
  simpa only [momentPanelPhase_owner2622K18P034] using h

theorem momentScalarAmp2622K18P034_radius_le :
    (momentScalarAmp2622K18P034Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentScalarAmp2622K18P034Expected]

def momentScalarGrow2622K18P034Input : RatPair2542 := (momentPanelGrowth2622K18P034 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K18P034Expected : RatState2542 :=
  ((((1106585112694133494498299883364314221914809195361917744561127057938119511820566680909469951577423 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1402762307545397736165555882333955397571964094755 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K18P034_replay :
    compactExp2620 momentScalarGrow2622K18P034Input 20 = momentScalarGrow2622K18P034Expected := by
  decide +kernel

theorem momentScalarGrow2622K18P034_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 18).re * (storedWidth 18 ^ 2)) (-111 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K18P034Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K18P034Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K18P034 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentPanelGrowth2622K18P034]
  have h := compactExp_real_error2620 momentPanelGrowth2622K18P034 20 hsmall
  change |Real.exp (momentPanelGrowth2622K18P034 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K18P034Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K18P034Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K18P034_replay] at h
  simpa only [momentPanelGrowth_owner2622K18P034] using h

theorem momentScalarGrow2622K18P034_radius_le :
    (momentScalarGrow2622K18P034Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, momentScalarGrow2622K18P034Expected]

end ConnesWeilRH.Dev
