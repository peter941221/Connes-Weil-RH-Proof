import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P173 : ℚ := ((-105067634204625969887358286491066076872947689760845667 : ℚ) / 1152359787090792007966460091733522373115429624217600)

def momentPanelGrowth2622K04P173 : ℚ := ((446195867714208790794142755180192851350779334440783 : ℚ) / 75501402944145277707983327783878292714647296409600)

theorem momentPanelPhase_owner2622K04P173 :
    (momentPanelPhase2622K04P173 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (167 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P173, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P173 :
    (momentPanelGrowth2622K04P173 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (167 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P173, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P173Input : RatPair2542 := (momentPanelPhase2622K04P173 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P173Expected : RatState2542 :=
  ((((539927487120958472023715893939479466914958318673979051553 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1208925819614629516994077 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P173_replay :
    compactExp2620 momentScalarAmp2622K04P173Input 20 = momentScalarAmp2622K04P173Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P173_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (167 / 200) 0) -
      (momentScalarAmp2622K04P173Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P173Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P173 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P173]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P173 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P173 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P173Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P173Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P173_replay] at h
  simpa only [momentPanelPhase_owner2622K04P173] using h

theorem momentScalarAmp2622K04P173_radius_le :
    (momentScalarAmp2622K04P173Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P173Expected]

def momentScalarGrow2622K04P173Input : RatPair2542 := (momentPanelGrowth2622K04P173 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P173Expected : RatState2542 :=
  ((((393684921672767603434449365775231271268468009797078955084112514270094778656713123966070800358567557 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((499052114596074950775211020719982430188969563028403 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P173_replay :
    compactExp2620 momentScalarGrow2622K04P173Input 20 = momentScalarGrow2622K04P173Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P173_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (167 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P173Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P173Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P173 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P173]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P173 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P173 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P173Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P173Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P173_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P173] using h

theorem momentScalarGrow2622K04P173_radius_le :
    (momentScalarGrow2622K04P173Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P173Expected]

end ConnesWeilRH.Dev
