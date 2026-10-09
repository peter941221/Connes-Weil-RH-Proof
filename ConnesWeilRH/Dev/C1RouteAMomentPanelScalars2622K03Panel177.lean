import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P177 : ℚ := ((-23336704966530128111136088997818246411864215213241 : ℚ) / 182687704666362864775460604089535377456991567872)

def momentPanelGrowth2622K03P177 : ℚ := ((6281681835313509986544882542115100898191134775192475 : ℚ) / 605335709411993352433488711650675473203741560143872)

theorem momentPanelPhase_owner2622K03P177 :
    (momentPanelPhase2622K03P177 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (7 / 8) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P177, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P177 :
    (momentPanelGrowth2622K03P177 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (7 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P177, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P177Input : RatPair2542 := (momentPanelPhase2622K03P177 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P177Expected : RatState2542 :=
  ((((35593390903846834017176268267928864504125 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P177_replay :
    compactExp2620 momentScalarAmp2622K03P177Input 20 = momentScalarAmp2622K03P177Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P177_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (7 / 8) 0) -
      (momentScalarAmp2622K03P177Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P177Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P177 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P177]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P177 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P177 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P177Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P177Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P177_replay] at h
  simpa only [momentPanelPhase_owner2622K03P177] using h

theorem momentScalarAmp2622K03P177_radius_le :
    (momentScalarAmp2622K03P177Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P177Expected]

def momentScalarGrow2622K03P177Input : RatPair2542 := (momentPanelGrowth2622K03P177 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P177Expected : RatState2542 :=
  ((((68604665411333258715345395396941284662548957332846712729792230030245144338793205930885875368779156897 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((43482942314382063127315331110854329304139305255156685 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P177_replay :
    compactExp2620 momentScalarGrow2622K03P177Input 20 = momentScalarGrow2622K03P177Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P177_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (7 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P177Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P177Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P177 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P177]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P177 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P177 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P177Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P177Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P177_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P177] using h

theorem momentScalarGrow2622K03P177_radius_le :
    (momentScalarGrow2622K03P177Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 67 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P177Expected]

end ConnesWeilRH.Dev
