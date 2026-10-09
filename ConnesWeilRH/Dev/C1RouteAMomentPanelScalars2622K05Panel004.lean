import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P004 : ℚ := ((-2460218866278666187176402240077908990221 : ℚ) / 21821844492568832209124847658624614400)

def momentPanelGrowth2622K05P004 : ℚ := ((1092201226123394510778934765879036219763 : ℚ) / 143261757873953026288987817371081113600)

theorem momentPanelPhase_owner2622K05P004 :
    (momentPanelPhase2622K05P004 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-171 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P004, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P004 :
    (momentPanelGrowth2622K05P004 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-171 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P004, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P004Input : RatPair2542 := (momentPanelPhase2622K05P004 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P004Expected : RatState2542 :=
  ((((29084978013687684569925213055531971008904396847 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((1208925819614629174706177 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P004_replay :
    compactExp2620 momentScalarAmp2622K05P004Input 20 = momentScalarAmp2622K05P004Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P004_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-171 / 200) 0) -
      (momentScalarAmp2622K05P004Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P004Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P004 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P004]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P004 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P004 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P004Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P004Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P004_replay] at h
  simpa only [momentPanelPhase_owner2622K05P004] using h

theorem momentScalarAmp2622K05P004_radius_le :
    (momentScalarAmp2622K05P004Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P004Expected]

def momentScalarGrow2622K05P004Input : RatPair2542 := (momentPanelGrowth2622K05P004 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P004Expected : RatState2542 :=
  ((((2185494247298731962769695940907909020047619831816323455297581196950782699945372504334985273802377679 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((173151434473146642468381485240683707724384491225753 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarGrow2622K05P004_replay :
    compactExp2620 momentScalarGrow2622K05P004Input 20 = momentScalarGrow2622K05P004Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P004_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-171 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P004Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P004Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P004 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P004]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P004 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P004 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P004Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P004Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P004_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P004] using h

theorem momentScalarGrow2622K05P004_radius_le :
    (momentScalarGrow2622K05P004Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 68 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P004Expected]

end ConnesWeilRH.Dev
