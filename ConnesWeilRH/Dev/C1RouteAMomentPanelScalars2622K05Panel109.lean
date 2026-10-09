import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P109 : ℚ := ((-2412412504140040193572142485016155418391 : ℚ) / 78044683913891262624306628223460966400)

def momentPanelGrowth2622K05P109 : ℚ := ((439074617220331552092462457103267 : ℚ) / 3042361440547750563592087692902400)

theorem momentPanelPhase_owner2622K05P109 :
    (momentPanelPhase2622K05P109 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (39 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P109, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P109 :
    (momentPanelGrowth2622K05P109 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (39 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P109, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P109Input : RatPair2542 := (momentPanelPhase2622K05P109 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P109Expected : RatState2542 :=
  ((((20100672207076900930506133362606835503896634779012382368162784988747564114182118367 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((101925521343194445295605150280991443 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P109_replay :
    compactExp2620 momentScalarAmp2622K05P109Input 20 = momentScalarAmp2622K05P109Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P109_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (39 / 200) 0) -
      (momentScalarAmp2622K05P109Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P109Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P109 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P109]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P109 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P109 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P109Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P109Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P109_replay] at h
  simpa only [momentPanelPhase_owner2622K05P109] using h

theorem momentScalarAmp2622K05P109_radius_le :
    (momentScalarAmp2622K05P109Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P109Expected]

def momentScalarGrow2622K05P109Input : RatPair2542 := (momentPanelGrowth2622K05P109 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P109Expected : RatState2542 :=
  ((((308450976780679795788116560333349416472025872397638677650734999099495803073328615771740809741277 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((1564032048163116904986294912586964952389193160673 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P109_replay :
    compactExp2620 momentScalarGrow2622K05P109Input 20 = momentScalarGrow2622K05P109Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P109_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (39 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P109Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P109Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P109 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P109]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P109 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P109 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P109Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P109Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P109_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P109] using h

theorem momentScalarGrow2622K05P109_radius_le :
    (momentScalarGrow2622K05P109Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P109Expected]

end ConnesWeilRH.Dev
