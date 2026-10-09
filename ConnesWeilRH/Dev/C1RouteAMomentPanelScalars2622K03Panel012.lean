import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P012 : ℚ := ((-2931930762854285710251692509838737107971023607303375 : ℚ) / 38912481093935290197173108671071035398339203956736)

def momentPanelGrowth2622K03P012 : ℚ := ((267439937261612742672691373714642142725360316501745425 : ℚ) / 87547693174066745239128618422089188352628227651403776)

theorem momentPanelPhase_owner2622K03P012 :
    (momentPanelPhase2622K03P012 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-31 / 40) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P012, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P012 :
    (momentPanelGrowth2622K03P012 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-31 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P012, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P012Input : RatPair2542 := (momentPanelPhase2622K03P012 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P012Expected : RatState2542 :=
  ((((2022418450456542654749758393851357475754131612576121885426104391 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851644357066937230681 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P012_replay :
    compactExp2620 momentScalarAmp2622K03P012Input 20 = momentScalarAmp2622K03P012Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P012_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-31 / 40) 0) -
      (momentScalarAmp2622K03P012Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P012Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P012 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P012]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P012 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P012 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P012Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P012Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P012_replay] at h
  simpa only [momentPanelPhase_owner2622K03P012] using h

theorem momentScalarAmp2622K03P012_radius_le :
    (momentScalarAmp2622K03P012Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P012Expected]

def momentScalarGrow2622K03P012Input : RatPair2542 := (momentPanelGrowth2622K03P012 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P012Expected : RatState2542 :=
  ((((45318721180736155188059157826923776744625078447712646913826610848556007696685202759023053456935239 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((57448136743810237919877205120472911360407445384527 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P012_replay :
    compactExp2620 momentScalarGrow2622K03P012Input 20 = momentScalarGrow2622K03P012Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P012_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-31 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P012Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P012Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P012 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P012]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P012 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P012 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P012Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P012Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P012_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P012] using h

theorem momentScalarGrow2622K03P012_radius_le :
    (momentScalarGrow2622K03P012Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P012Expected]

end ConnesWeilRH.Dev
