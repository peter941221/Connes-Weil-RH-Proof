import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K08
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K08P049 : ℚ := ((-2476431670658440570452304980865213493271 : ℚ) / 67822349473650820730637213575308902400)

def momentPanelGrowth2622K08P049 : ℚ := ((8678119266725270494028285692024416563603 : ℚ) / 23394326525573703843507702485116098969600)

theorem momentPanelPhase_owner2622K08P049 :
    (momentPanelPhase2622K08P049 : ℝ) = momentPhase2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2)) (-81 / 200) 0 := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelPhase2622K08P049, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K08P049 :
    (momentPanelGrowth2622K08P049 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2))
      (-81 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelGrowth2622K08P049, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K08P049Input : RatPair2542 := (momentPanelPhase2622K08P049 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K08P049Expected : RatState2542 :=
  ((((74118231952716182355689251380480823480919918858849910331318709966344360238242639 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((187918587239842330911757977110899 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K08P049_replay :
    compactExp2620 momentScalarAmp2622K08P049Input 20 = momentScalarAmp2622K08P049Expected := by
  decide +kernel

theorem momentScalarAmp2622K08P049_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2)) (-81 / 200) 0) -
      (momentScalarAmp2622K08P049Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K08P049Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K08P049 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelPhase2622K08P049]
  have h := compactExp_real_error2620 momentPanelPhase2622K08P049 20 hsmall
  change |Real.exp (momentPanelPhase2622K08P049 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K08P049Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K08P049Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K08P049_replay] at h
  simpa only [momentPanelPhase_owner2622K08P049] using h

theorem momentScalarAmp2622K08P049_radius_le :
    (momentScalarAmp2622K08P049Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentScalarAmp2622K08P049Expected]

def momentScalarGrow2622K08P049Input : RatPair2542 := (momentPanelGrowth2622K08P049 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K08P049Expected : RatState2542 :=
  ((((193455042170972578289209034721137088472436400478338056973092410938780935925659173749071008458255 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((1961866508561394172537273980515562245967782597085 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K08P049_replay :
    compactExp2620 momentScalarGrow2622K08P049Input 20 = momentScalarGrow2622K08P049Expected := by
  decide +kernel

theorem momentScalarGrow2622K08P049_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 8).re * (storedWidth 8 ^ 2)) (-81 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K08P049Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K08P049Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K08P049 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentPanelGrowth2622K08P049]
  have h := compactExp_real_error2620 momentPanelGrowth2622K08P049 20 hsmall
  change |Real.exp (momentPanelGrowth2622K08P049 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K08P049Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K08P049Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K08P049_replay] at h
  simpa only [momentPanelGrowth_owner2622K08P049] using h

theorem momentScalarGrow2622K08P049_radius_le :
    (momentScalarGrow2622K08P049Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, momentScalarGrow2622K08P049Expected]

end ConnesWeilRH.Dev
