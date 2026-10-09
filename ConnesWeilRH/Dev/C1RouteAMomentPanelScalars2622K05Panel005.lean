import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P005 : ℚ := ((-820518522450869486762020659822852328333 : ℚ) / 7733682781872381932651086915357900800)

def momentPanelGrowth2622K05P005 : ℚ := ((27642853439530766280555034512706212523 : ℚ) / 4164992812109870521557568051583385600)

theorem momentPanelPhase_owner2622K05P005 :
    (momentPanelPhase2622K05P005 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-169 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P005, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P005 :
    (momentPanelGrowth2622K05P005 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-169 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P005, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P005Input : RatPair2542 := (momentPanelPhase2622K05P005 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P005Expected : RatState2542 :=
  ((((178801180714845604006121721243501962797036712558863 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349412623 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P005_replay :
    compactExp2620 momentScalarAmp2622K05P005Input 20 = momentScalarAmp2622K05P005Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P005_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-169 / 200) 0) -
      (momentScalarAmp2622K05P005Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P005Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P005 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P005]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P005 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P005 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P005Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P005Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P005_replay] at h
  simpa only [momentPanelPhase_owner2622K05P005] using h

theorem momentScalarAmp2622K05P005_radius_le :
    (momentScalarAmp2622K05P005Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P005Expected]

def momentScalarGrow2622K05P005Input : RatPair2542 := (momentPanelGrowth2622K05P005 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P005Expected : RatState2542 :=
  ((((407314472135777248105910908092586914597485076930417437813947023615966854287496654438038361122352563 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2065316667896176966405395897780110498640097491062031 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P005_replay :
    compactExp2620 momentScalarGrow2622K05P005Input 20 = momentScalarGrow2622K05P005Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P005_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-169 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P005Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P005Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P005 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P005]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P005 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P005 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P005Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P005Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P005_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P005] using h

theorem momentScalarGrow2622K05P005_radius_le :
    (momentScalarGrow2622K05P005Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P005Expected]

end ConnesWeilRH.Dev
