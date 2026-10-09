import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P145 : ℚ := ((-87293430907213131988816953461698658325 : ℚ) / 2245587261677898342657743873382547456)

def momentPanelGrowth2622K07P145 : ℚ := ((1975624795485794260890460233399583025 : ℚ) / 2488529963910438050995784049286447104)

theorem momentPanelPhase_owner2622K07P145 :
    (momentPanelPhase2622K07P145 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (111 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P145, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P145 :
    (momentPanelGrowth2622K07P145 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (111 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P145, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P145Input : RatPair2542 := (momentPanelPhase2622K07P145 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P145Expected : RatState2542 :=
  ((((27998224747878832501359871347041676809476640346676948002399644154934623243674975 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((35493284624654184285509281229789 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P145_replay :
    compactExp2620 momentScalarAmp2622K07P145Input 20 = momentScalarAmp2622K07P145Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P145_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (111 / 200) 0) -
      (momentScalarAmp2622K07P145Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P145Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P145 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P145]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P145 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P145 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P145Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P145Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P145_replay] at h
  simpa only [momentPanelPhase_owner2622K07P145] using h

theorem momentScalarAmp2622K07P145_radius_le :
    (momentScalarAmp2622K07P145Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P145Expected]

def momentScalarGrow2622K07P145Input : RatPair2542 := (momentPanelGrowth2622K07P145 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P145Expected : RatState2542 :=
  ((((4724780757386357724110566848637175131234016078238695992078662137557363276227237487190081067053687 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5989366628408347873027971213928354399675034540141 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P145_replay :
    compactExp2620 momentScalarGrow2622K07P145Input 20 = momentScalarGrow2622K07P145Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P145_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (111 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P145Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P145Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P145 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P145]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P145 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P145 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P145Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P145Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P145_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P145] using h

theorem momentScalarGrow2622K07P145_radius_le :
    (momentScalarGrow2622K07P145Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P145Expected]

end ConnesWeilRH.Dev
