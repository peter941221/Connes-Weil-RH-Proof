import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P008 : ℚ := ((-73272411669239387328259917541561470186948969723832175 : ℚ) / 817892853791306545599737124508849884874951249362944)

def momentPanelGrowth2622K03P008 : ℚ := ((93687908138784692188131741083460485996785273076680475 : ℚ) / 20423297911619036923275455043283473219738186842898432)

theorem momentPanelPhase_owner2622K03P008 :
    (momentPanelPhase2622K03P008 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-163 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P008, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P008 :
    (momentPanelGrowth2622K03P008 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-163 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P008, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P008Input : RatPair2542 := (momentPanelPhase2622K03P008 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P008Expected : RatState2542 :=
  ((((1322852416774219702933646176180849906360080612423280007493 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1208925819614630851849207 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K03P008_replay :
    compactExp2620 momentScalarAmp2622K03P008Input 20 = momentScalarAmp2622K03P008Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P008_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-163 / 200) 0) -
      (momentScalarAmp2622K03P008Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P008Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P008 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P008]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P008 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P008 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P008Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P008Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P008_replay] at h
  simpa only [momentPanelPhase_owner2622K03P008] using h

theorem momentScalarAmp2622K03P008_radius_le :
    (momentScalarAmp2622K03P008Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P008Expected]

def momentScalarGrow2622K03P008Input : RatPair2542 := (momentPanelGrowth2622K03P008 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P008Expected : RatState2542 :=
  ((((209816725813124232010534797583228690172119427583695840282078500357004791562166455177837080148904059 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((265973134834310805249489059231228796932826225756889 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P008_replay :
    compactExp2620 momentScalarGrow2622K03P008Input 20 = momentScalarGrow2622K03P008Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P008_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-163 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P008Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P008Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P008 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P008]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P008 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P008 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P008Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P008Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P008_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P008] using h

theorem momentScalarGrow2622K03P008_radius_le :
    (momentScalarGrow2622K03P008Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P008Expected]

end ConnesWeilRH.Dev
