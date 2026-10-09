import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P080 : ℚ := ((-73142966740943373833521988633228539238852231247230975 : ℚ) / 2413852641756652532278160961835030942339229586292736)

def momentPanelGrowth2622K03P080 : ℚ := ((19152190243247879627611265093944023322239241271675 : ℚ) / 298420365572503739610714896780256039075995726118912)

theorem momentPanelPhase_owner2622K03P080 :
    (momentPanelPhase2622K03P080 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-19 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P080, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P080 :
    (momentPanelGrowth2622K03P080 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-19 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P080, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P080Input : RatPair2542 := (momentPanelPhase2622K03P080 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P080Expected : RatState2542 :=
  ((((147874868690138596033575105037959498828171500754902992375937352584286395302460926147 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((46864770774270046097214778664768529 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K03P080_replay :
    compactExp2620 momentScalarAmp2622K03P080Input 20 = momentScalarAmp2622K03P080Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P080_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-19 / 200) 0) -
      (momentScalarAmp2622K03P080Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P080Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P080 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P080]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P080 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P080 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P080Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P080Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P080_replay] at h
  simpa only [momentPanelPhase_owner2622K03P080] using h

theorem momentScalarAmp2622K03P080_radius_le :
    (momentScalarAmp2622K03P080Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P080Expected]

def momentScalarGrow2622K03P080Input : RatPair2542 := (momentPanelGrowth2622K03P080 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P080Expected : RatState2542 :=
  ((((1138783097838148344796706700164475671035110022526077380811175511671826654324734410663738428080109 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1443578989149390914986791430396196630479366383697 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P080_replay :
    compactExp2620 momentScalarGrow2622K03P080Input 20 = momentScalarGrow2622K03P080Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P080_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-19 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P080Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P080Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P080 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P080]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P080 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P080 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P080Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P080Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P080_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P080] using h

theorem momentScalarGrow2622K03P080_radius_le :
    (momentScalarGrow2622K03P080Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P080Expected]

end ConnesWeilRH.Dev
