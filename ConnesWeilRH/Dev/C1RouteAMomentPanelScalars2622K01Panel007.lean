import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P007 : ℚ := ((-686199291037766208668236473776301562497984304831599 : ℚ) / 7293235709727454992207841303886920146915835248640)

def momentPanelGrowth2622K01P007 : ℚ := ((592522139004975526730479227885763795957466697178539211 : ℚ) / 115111344304313652850032594351070060148758339072819200)

theorem momentPanelPhase_owner2622K01P007 :
    (momentPanelPhase2622K01P007 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-33 / 40) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P007, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P007 :
    (momentPanelGrowth2622K01P007 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-33 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P007, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P007Input : RatPair2542 := (momentPanelPhase2622K01P007 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P007Expected : RatState2542 :=
  ((((14691515943439008370758956027882979901513553054056123039 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((302231454903657298335131 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K01P007_replay :
    compactExp2620 momentScalarAmp2622K01P007Input 20 = momentScalarAmp2622K01P007Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P007_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-33 / 40) 0) -
      (momentScalarAmp2622K01P007Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P007Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P007 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P007]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P007 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P007 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P007Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P007Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P007_replay] at h
  simpa only [momentPanelPhase_owner2622K01P007] using h

theorem momentScalarAmp2622K01P007_radius_le :
    (momentScalarAmp2622K01P007Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P007Expected]

def momentScalarGrow2622K01P007Input : RatPair2542 := (momentPanelGrowth2622K01P007 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P007Expected : RatState2542 :=
  ((((183674348236716099439858355031402614704019551922881649776384394976523728814433233011564677693698927 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((232833754822172363938420345905808952216843480555207 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P007_replay :
    compactExp2620 momentScalarGrow2622K01P007Input 20 = momentScalarGrow2622K01P007Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P007_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-33 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P007Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P007Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P007 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P007]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P007 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P007 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P007Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P007Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P007_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P007] using h

theorem momentScalarGrow2622K01P007_radius_le :
    (momentScalarGrow2622K01P007Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 69 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P007Expected]

end ConnesWeilRH.Dev
