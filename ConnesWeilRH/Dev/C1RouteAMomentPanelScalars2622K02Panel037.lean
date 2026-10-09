import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P037 : ℚ := ((-2882339183672841773443495818087063339553795309409181 : ℚ) / 66167203033848300085862137543678594522704133488640)

def momentPanelGrowth2622K02P037 : ℚ := ((1613463369374614238654664820434081613859563798434584533 : ℚ) / 2460122156532179233874225217192823290317080934272204800)

theorem momentPanelPhase_owner2622K02P037 :
    (momentPanelPhase2622K02P037 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-21 / 40) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P037, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P037 :
    (momentPanelGrowth2622K02P037 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-21 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P037, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P037Input : RatPair2542 := (momentPanelPhase2622K02P037 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P037Expected : RatState2542 :=
  ((((128846333596965430814929582734759507922215319800276256882011425499823197885165 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((326680253131725288440414958921 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P037_replay :
    compactExp2620 momentScalarAmp2622K02P037Input 20 = momentScalarAmp2622K02P037Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P037_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-21 / 40) 0) -
      (momentScalarAmp2622K02P037Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P037Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P037 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P037]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P037 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P037 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P037Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P037Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P037_replay] at h
  simpa only [momentPanelPhase_owner2622K02P037] using h

theorem momentScalarAmp2622K02P037_radius_le :
    (momentScalarAmp2622K02P037Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P037Expected]

def momentScalarGrow2622K02P037Input : RatPair2542 := (momentPanelGrowth2622K02P037 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P037Expected : RatState2542 :=
  ((((2057781626416428216708190106307396879478095664204129946459854917022733315173557334968988480927773 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((5217092964624409401670291830130948898377315563997 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P037_replay :
    compactExp2620 momentScalarGrow2622K02P037Input 20 = momentScalarGrow2622K02P037Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P037_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-21 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P037Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P037Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P037 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P037]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P037 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P037 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P037Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P037Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P037_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P037] using h

theorem momentScalarGrow2622K02P037_radius_le :
    (momentScalarGrow2622K02P037Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P037Expected]

end ConnesWeilRH.Dev
