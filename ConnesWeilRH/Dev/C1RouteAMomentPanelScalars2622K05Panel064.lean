import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P064 : ℚ := ((-2461185735559361889316491445804040963061 : ℚ) / 75854183676696882218520325084571238400)

def momentPanelGrowth2622K05P064 : ℚ := ((355509539006281720647309622200243562643 : ℚ) / 1836761830140452900006887510748273049600)

theorem momentPanelPhase_owner2622K05P064 :
    (momentPanelPhase2622K05P064 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-51 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P064, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P064 :
    (momentPanelGrowth2622K05P064 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-51 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P064, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P064Input : RatPair2542 := (momentPanelPhase2622K05P064 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P064Expected : RatState2542 :=
  ((((4328129500118445312371849669105428865666391082105044977986856164820977054193553245 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((10973451466815662884981425939429861 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P064_replay :
    compactExp2620 momentScalarAmp2622K05P064Input 20 = momentScalarAmp2622K05P064Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P064_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-51 / 200) 0) -
      (momentScalarAmp2622K05P064Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P064Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P064 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P064]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P064 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P064 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P064Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P064Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P064_replay] at h
  simpa only [momentPanelPhase_owner2622K05P064] using h

theorem momentScalarAmp2622K05P064_radius_le :
    (momentScalarAmp2622K05P064Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P064Expected]

def momentScalarGrow2622K05P064Input : RatPair2542 := (momentPanelGrowth2622K05P064 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P064Expected : RatState2542 :=
  ((((1296066625371862529266382186363179286167464917646808214910149128383732912057909896285342200950871 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1642959332321279208666521876130698524259927000627 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P064_replay :
    compactExp2620 momentScalarGrow2622K05P064Input 20 = momentScalarGrow2622K05P064Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P064_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-51 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P064Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P064Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P064 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P064]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P064 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P064 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P064Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P064Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P064_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P064] using h

theorem momentScalarGrow2622K05P064_radius_le :
    (momentScalarGrow2622K05P064Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P064Expected]

end ConnesWeilRH.Dev
