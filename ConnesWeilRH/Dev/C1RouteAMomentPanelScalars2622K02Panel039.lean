import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P039 : ℚ := ((-120033908683267448775383269385064592025124122273036207 : ℚ) / 2835370266329659899710390906908367037937964443238400)

def momentPanelGrowth2622K02P039 : ℚ := ((4686828668038655682249558531197248719829076026093768479 : ℚ) / 7813496181397400758647195811299247058979587686295142400)

theorem momentPanelPhase_owner2622K02P039 :
    (momentPanelPhase2622K02P039 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-101 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P039, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P039 :
    (momentPanelGrowth2622K02P039 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-101 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P039, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P039Input : RatPair2542 := (momentPanelPhase2622K02P039 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P039Expected : RatState2542 :=
  ((((13733783820338622424230272686751808985633686573797272140647636398522932403471 : ℚ) / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384), 0), ((1114264318782546222057949718461 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P039_replay :
    compactExp2620 momentScalarAmp2622K02P039Input 20 = momentScalarAmp2622K02P039Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P039_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-101 / 200) 0) -
      (momentScalarAmp2622K02P039Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P039Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P039 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P039]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P039 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P039 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P039Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P039Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P039_replay] at h
  simpa only [momentPanelPhase_owner2622K02P039] using h

theorem momentScalarAmp2622K02P039_radius_le :
    (momentScalarAmp2622K02P039Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P039Expected]

def momentScalarGrow2622K02P039Input : RatPair2542 := (momentPanelGrowth2622K02P039 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P039Expected : RatState2542 :=
  ((((1945695029105780775162951611113254042734324058913939311855612557581341053694890157390230063993895 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1233230030284445245864277998605399264500552523747 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K02P039_replay :
    compactExp2620 momentScalarGrow2622K02P039Input 20 = momentScalarGrow2622K02P039Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P039_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-101 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P039Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P039Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P039 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P039]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P039 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P039 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P039Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P039Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P039_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P039] using h

theorem momentScalarGrow2622K02P039_radius_le :
    (momentScalarGrow2622K02P039Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P039Expected]

end ConnesWeilRH.Dev
