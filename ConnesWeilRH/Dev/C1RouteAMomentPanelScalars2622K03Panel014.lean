import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P014 : ℚ := ((-73309168638040846489592841754368365407454095761219275 : ℚ) / 1047348610852258303757715643245306318960932658610176)

def momentPanelGrowth2622K03P014 : ℚ := ((84840989507373211621176307734396049897896701298275 : ℚ) / 33157818396944859956746099642250671008443969568768)

theorem momentPanelPhase_owner2622K03P014 :
    (momentPanelPhase2622K03P014 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-151 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P014, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P014 :
    (momentPanelGrowth2622K03P014 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-151 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P014, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P014Input : RatPair2542 := (momentPanelPhase2622K03P014 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P014Expected : RatState2542 :=
  ((((853405160420269509779568425671518154440665443658971058655284952123 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((302231590140130219036787 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K03P014_replay :
    compactExp2620 momentScalarAmp2622K03P014Input 20 = momentScalarAmp2622K03P014Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P014_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-151 / 200) 0) -
      (momentScalarAmp2622K03P014Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P014Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P014 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P014]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P014 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P014 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P014Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P014Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P014_replay] at h
  simpa only [momentPanelPhase_owner2622K03P014] using h

theorem momentScalarAmp2622K03P014_radius_le :
    (momentScalarAmp2622K03P014Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P014Expected]

def momentScalarGrow2622K03P014Input : RatPair2542 := (momentPanelGrowth2622K03P014 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P014Expected : RatState2542 :=
  ((((27594907688048423852866569436372641015828710826283680577173008542634681829089321637529762033801525 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((17490307967643369044019929816350122132065417723333 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P014_replay :
    compactExp2620 momentScalarGrow2622K03P014Input 20 = momentScalarGrow2622K03P014Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P014_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-151 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P014Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P014Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P014 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P014]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P014 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P014 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P014Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P014Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P014_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P014] using h

theorem momentScalarGrow2622K03P014_radius_le :
    (momentScalarGrow2622K03P014Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P014Expected]

end ConnesWeilRH.Dev
