import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P087 : ℚ := ((-228395044010990502824880410754379632016297500413509 : ℚ) / 7607230202122766166040664217165809076920039505920)

def momentPanelGrowth2622K01P087 : ℚ := ((70858315590366619811105094061447140356584591980478113 : ℚ) / 3561699507324300612749711779790303248070795375253913600)

theorem momentPanelPhase_owner2622K01P087 :
    (momentPanelPhase2622K01P087 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-1 / 40) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P087, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P087 :
    (momentPanelGrowth2622K01P087 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-1 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P087, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P087Input : RatPair2542 := (momentPanelPhase2622K01P087 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P087Expected : RatState2542 :=
  ((((97625735301207258932698510914267418496152296029132586528928302999236980864529786549 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((30939716359029139970250172971353831 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K01P087_replay :
    compactExp2620 momentScalarAmp2622K01P087Input 20 = momentScalarAmp2622K01P087Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P087_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-1 / 40) 0) -
      (momentScalarAmp2622K01P087Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P087Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P087 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P087]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P087 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P087 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P087Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P087Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P087_replay] at h
  simpa only [momentPanelPhase_owner2622K01P087] using h

theorem momentScalarAmp2622K01P087_radius_le :
    (momentScalarAmp2622K01P087Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P087Expected]

def momentScalarGrow2622K01P087Input : RatPair2542 := (momentPanelGrowth2622K01P087 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P087Expected : RatState2542 :=
  ((((2178907001358547527837335481514330252764200181354058267042502723814803446959035960174949955016583 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1381046357854377451205410192663427524558698843447 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P087_replay :
    compactExp2620 momentScalarGrow2622K01P087Input 20 = momentScalarGrow2622K01P087Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P087_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-1 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P087Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P087Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P087 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P087]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P087 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P087 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P087Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P087Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P087_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P087] using h

theorem momentScalarGrow2622K01P087_radius_le :
    (momentScalarGrow2622K01P087Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P087Expected]

end ConnesWeilRH.Dev
