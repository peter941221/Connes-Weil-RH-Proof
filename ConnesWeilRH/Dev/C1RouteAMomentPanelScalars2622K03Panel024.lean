import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P024 : ℚ := ((-73344759611716272841111538491631434801878401215717775 : ℚ) / 1390801495625020489535581578933632828580076806209536)

def momentPanelGrowth2622K03P024 : ℚ := ((226614393565049918941671361159406072619412361091589425 : ℚ) / 181858393831029910550812400677270931611025554649645056)

theorem momentPanelPhase_owner2622K03P024 :
    (momentPanelPhase2622K03P024 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-131 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P024, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P024 :
    (momentPanelGrowth2622K03P024 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-131 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P024, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P024Input : RatPair2542 := (momentPanelPhase2622K03P024 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P024Expected : RatState2542 :=
  ((((3339842344419136962781879458914173454289843588147583902519700629254431033 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((18144790157018789308025081 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K03P024_replay :
    compactExp2620 momentScalarAmp2622K03P024Input 20 = momentScalarAmp2622K03P024Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P024_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-131 / 200) 0) -
      (momentScalarAmp2622K03P024Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P024Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P024 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P024]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P024 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P024 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P024Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P024Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P024_replay] at h
  simpa only [momentPanelPhase_owner2622K03P024] using h

theorem momentScalarAmp2622K03P024_radius_le :
    (momentScalarAmp2622K03P024Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 94 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P024Expected]

def momentScalarGrow2622K03P024Input : RatPair2542 := (momentPanelGrowth2622K03P024 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P024Expected : RatState2542 :=
  ((((7426334658574988187671479899422017827354171660791335982458836441078392833358967423075539129925325 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1176748300008376763108657026014486400078050685849 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K03P024_replay :
    compactExp2620 momentScalarGrow2622K03P024Input 20 = momentScalarGrow2622K03P024Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P024_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-131 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P024Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P024Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P024 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P024]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P024 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P024 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P024Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P024Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P024_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P024] using h

theorem momentScalarGrow2622K03P024_radius_le :
    (momentScalarGrow2622K03P024Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P024Expected]

end ConnesWeilRH.Dev
