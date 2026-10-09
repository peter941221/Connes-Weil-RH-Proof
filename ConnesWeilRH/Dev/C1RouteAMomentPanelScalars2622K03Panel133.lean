import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P133 : ℚ := ((-218462292967419251554204538552044044597379437995927775 : ℚ) / 5924744950034814067532962851227721826307693537656832)

def momentPanelGrowth2622K03P133 : ℚ := ((49419387941345619377107464741682046497045048586275 : ℚ) / 120847916636799035048967189605227652187799922147328)

theorem momentPanelPhase_owner2622K03P133 :
    (momentPanelPhase2622K03P133 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (87 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P133, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P133 :
    (momentPanelGrowth2622K03P133 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (87 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P133, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P133Input : RatPair2542 := (momentPanelPhase2622K03P133 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P133Expected : RatState2542 :=
  ((((206975454057392638920279957841286137267260154722888241487318832096610787801035187 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((262381787400710054406577991670875 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P133_replay :
    compactExp2620 momentScalarAmp2622K03P133Input 20 = momentScalarAmp2622K03P133Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P133_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (87 / 200) 0) -
      (momentScalarAmp2622K03P133Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P133Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P133 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P133]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P133 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P133 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P133Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P133Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P133_replay] at h
  simpa only [momentPanelPhase_owner2622K03P133] using h

theorem momentScalarAmp2622K03P133_radius_le :
    (momentScalarAmp2622K03P133Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P133Expected]

def momentScalarGrow2622K03P133Input : RatPair2542 := (momentPanelGrowth2622K03P133 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P133Expected : RatState2542 :=
  ((((1607564586841193701559645627683413629851414052831896780562651356367816705187342158198218360871023 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2037829418672832470327518692700993153615992156335 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K03P133_replay :
    compactExp2620 momentScalarGrow2622K03P133Input 20 = momentScalarGrow2622K03P133Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P133_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (87 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P133Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P133Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P133 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P133]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P133 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P133 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P133Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P133Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P133_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P133] using h

theorem momentScalarGrow2622K03P133_radius_le :
    (momentScalarGrow2622K03P133Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P133Expected]

end ConnesWeilRH.Dev
