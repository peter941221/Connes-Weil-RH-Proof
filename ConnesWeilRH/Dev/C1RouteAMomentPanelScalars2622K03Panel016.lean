import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P016 : ℚ := ((-219956284793824167456466048864027706384266177124953725 : ℚ) / 3359809576519079446085495969810645126811531924733952)

def momentPanelGrowth2622K03P016 : ℚ := ((84608361451746570709638240572928030094527163655670475 : ℚ) / 38947831164788231411507160297962360493877131825119232)

theorem momentPanelPhase_owner2622K03P016 :
    (momentPanelPhase2622K03P016 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-147 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P016, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P016 :
    (momentPanelGrowth2622K03P016 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-147 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P016, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P016Input : RatPair2542 := (momentPanelPhase2622K03P016 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P016Expected : RatState2542 :=
  ((((19752835177580514597134710211761402217198950652827823571356754551527 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2417951804256281309361367 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P016_replay :
    compactExp2620 momentScalarAmp2622K03P016Input 20 = momentScalarAmp2622K03P016Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P016_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-147 / 200) 0) -
      (momentScalarAmp2622K03P016Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P016Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P016 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P016]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P016 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P016 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P016Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P016Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P016_replay] at h
  simpa only [momentPanelPhase_owner2622K03P016] using h

theorem momentScalarAmp2622K03P016_radius_le :
    (momentScalarAmp2622K03P016Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P016Expected]

def momentScalarGrow2622K03P016Input : RatPair2542 := (momentPanelGrowth2622K03P016 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P016Expected : RatState2542 :=
  ((((9375807570653227731931164133391772365619809189830617661344997660570428621619298561331422397743815 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((11885223471737044218625016922833812353962252369549 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P016_replay :
    compactExp2620 momentScalarGrow2622K03P016Input 20 = momentScalarGrow2622K03P016Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P016_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-147 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P016Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P016Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P016 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P016]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P016 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P016 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P016Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P016Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P016_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P016] using h

theorem momentScalarGrow2622K03P016_radius_le :
    (momentScalarGrow2622K03P016Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P016Expected]

end ConnesWeilRH.Dev
