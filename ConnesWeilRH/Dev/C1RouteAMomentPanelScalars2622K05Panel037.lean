import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P037 : ℚ := ((-19819435176623020634633398803674325171 : ℚ) / 470146254612645720427097284809850880)

def momentPanelGrowth2622K05P037 : ℚ := ((10996357944330978241095941992552751684603 : ℚ) / 17480219274064120567929771377129265561600)

theorem momentPanelPhase_owner2622K05P037 :
    (momentPanelPhase2622K05P037 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-21 / 40) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P037, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P037 :
    (momentPanelGrowth2622K05P037 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-21 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P037, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P037Input : RatPair2542 := (momentPanelPhase2622K05P037 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P037Expected : RatState2542 :=
  ((((262704151908097445517689320928180338687177761693393436915091928780792651256897 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((666062137727501211590216806281 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P037_replay :
    compactExp2620 momentScalarAmp2622K05P037Input 20 = momentScalarAmp2622K05P037Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P037_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-21 / 40) 0) -
      (momentScalarAmp2622K05P037Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P037Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P037 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P037]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P037 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P037 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P037Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P037Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P037_replay] at h
  simpa only [momentPanelPhase_owner2622K05P037] using h

theorem momentScalarAmp2622K05P037_radius_le :
    (momentScalarAmp2622K05P037Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P037Expected]

def momentScalarGrow2622K05P037Input : RatPair2542 := (momentPanelGrowth2622K05P037 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P037Expected : RatState2542 :=
  ((((500855161272470234676733193710525080119007743376568722330945955807796822514918110342609664410429 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((2539635859648357014171847658716611328283677693323 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P037_replay :
    compactExp2620 momentScalarGrow2622K05P037Input 20 = momentScalarGrow2622K05P037Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P037_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-21 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P037Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P037Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P037 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P037]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P037 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P037 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P037Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P037Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P037_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P037] using h

theorem momentScalarGrow2622K05P037_radius_le :
    (momentScalarGrow2622K05P037Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P037Expected]

end ConnesWeilRH.Dev
