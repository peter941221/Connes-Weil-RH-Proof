import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P099 : ℚ := ((-1813008014925151622512919418130393936937435841204944863 : ℚ) / 60346316043916313306954024045875773558480739657318400)

def momentPanelGrowth2622P099 : ℚ := ((637203898764157455567295535339150674202141569150757 : ℚ) / 7460509139312593490267872419506400976899893152972800)

theorem momentPanelPhase_owner2622P099 :
    (momentPanelPhase2622P099 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (19 / 200) 0 := by
  norm_num [momentPanelPhase2622P099, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P099 :
    (momentPanelGrowth2622P099 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (19 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P099, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P099Input : RatPair2542 := (momentPanelPhase2622P099 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P099Expected : RatState2542 :=
  ((((191390046559336026839077571523383990624555124468384329077461858066121973442282187557 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((121311329415775559835963026972653043 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622P099_replay :
    compactExp2620 momentScalarAmp2622P099Input 20 = momentScalarAmp2622P099Expected := by
  decide +kernel

theorem momentScalarAmp2622P099_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (19 / 200) 0) -
      (momentScalarAmp2622P099Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P099Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P099 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P099]
  have h := compactExp_real_error2620 momentPanelPhase2622P099 20 hsmall
  change |Real.exp (momentPanelPhase2622P099 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P099Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P099Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P099_replay] at h
  simpa only [momentPanelPhase_owner2622P099] using h

theorem momentScalarAmp2622P099_radius_le :
    (momentScalarAmp2622P099Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622P099Expected]

def momentScalarGrow2622P099Input : RatPair2542 := (momentPanelGrowth2622P099 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P099Expected : RatState2542 :=
  ((((1163219875109215036766181469933472456242482483637813756456311505924956280444245962135112416480849 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1474556252771748573889260829440124673361088187203 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622P099_replay :
    compactExp2620 momentScalarGrow2622P099Input 20 = momentScalarGrow2622P099Expected := by
  decide +kernel

theorem momentScalarGrow2622P099_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (19 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P099Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P099Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P099 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P099]
  have h := compactExp_real_error2620 momentPanelGrowth2622P099 20 hsmall
  change |Real.exp (momentPanelGrowth2622P099 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P099Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P099Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P099_replay] at h
  simpa only [momentPanelGrowth_owner2622P099] using h

theorem momentScalarGrow2622P099_radius_le :
    (momentScalarGrow2622P099Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P099Expected]

end ConnesWeilRH.Dev
