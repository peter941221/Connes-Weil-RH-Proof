import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P080 : ℚ := ((-117572958419583551387170261608367542690689196138667769 : ℚ) / 3771644752744769581684626502867235847405046228582400)

def momentPanelGrowth2622K04P080 : ℚ := ((72701618507151450022077196917965405822640915727709 : ℚ) / 466281821207037093141742026219150061056243322060800)

theorem momentPanelPhase_owner2622K04P080 :
    (momentPanelPhase2622K04P080 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-19 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P080, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P080 :
    (momentPanelGrowth2622K04P080 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-19 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P080, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P080Input : RatPair2542 := (momentPanelPhase2622K04P080 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P080Expected : RatState2542 :=
  ((((15464540186956731799396993415040793236284912204633013165876451512068926175311577699 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((39208432902359732512715156035457161 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P080_replay :
    compactExp2620 momentScalarAmp2622K04P080Input 20 = momentScalarAmp2622K04P080Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P080_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-19 / 200) 0) -
      (momentScalarAmp2622K04P080Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P080Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P080 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P080]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P080 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P080 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P080Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P080Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P080_replay] at h
  simpa only [momentPanelPhase_owner2622K04P080] using h

theorem momentScalarAmp2622K04P080_radius_le :
    (momentScalarAmp2622K04P080Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P080Expected]

def momentScalarGrow2622K04P080Input : RatPair2542 := (momentPanelGrowth2622K04P080 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P080Expected : RatState2542 :=
  ((((1248196156439618914130985230212483901802749575107423688123277697641237880454826554470401740587787 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3164552743274038852014757458104615188553384649523 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P080_replay :
    compactExp2620 momentScalarGrow2622K04P080Input 20 = momentScalarGrow2622K04P080Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P080_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-19 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P080Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P080Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P080 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P080]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P080 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P080 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P080Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P080Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P080_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P080] using h

theorem momentScalarGrow2622K04P080_radius_le :
    (momentScalarGrow2622K04P080Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P080Expected]

end ConnesWeilRH.Dev
