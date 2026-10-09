import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P119 : ℚ := ((-109988913838416740307880992934534676552095981081298447 : ℚ) / 3474777232661929926424503021221740859037434930790400)

def momentPanelGrowth2622K02P119 : ℚ := ((305226107545963426431477132605076699388648340879799 : ℚ) / 1181903814329805377504366611301126922438552479334400)

theorem momentPanelPhase_owner2622K02P119 :
    (momentPanelPhase2622K02P119 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (59 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P119, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P119 :
    (momentPanelGrowth2622K02P119 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (59 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P119, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P119Input : RatPair2542 := (momentPanelPhase2622K02P119 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P119Expected : RatState2542 :=
  ((((38251779381655048927614538477503655721728017484262180735310933156444857172483090011 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((48491354888810720453047756787182301 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P119_replay :
    compactExp2620 momentScalarAmp2622K02P119Input 20 = momentScalarAmp2622K02P119Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P119_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (59 / 200) 0) -
      (momentScalarAmp2622K02P119Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P119Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P119 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P119]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P119 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P119 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P119Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P119Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P119_replay] at h
  simpa only [momentPanelPhase_owner2622K02P119] using h

theorem momentScalarAmp2622K02P119_radius_le :
    (momentScalarAmp2622K02P119Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P119Expected]

def momentScalarGrow2622K02P119Input : RatPair2542 := (momentPanelGrowth2622K02P119 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P119Expected : RatState2542 :=
  ((((1382690451537647067331976251559030537209762798400525229586882025817316294764711993983889554734547 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((438191987284843386650088130828333377821912902103 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K02P119_replay :
    compactExp2620 momentScalarGrow2622K02P119Input 20 = momentScalarGrow2622K02P119Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P119_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (59 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P119Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P119Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P119 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P119]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P119 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P119 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P119Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P119Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P119_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P119] using h

theorem momentScalarGrow2622K02P119_radius_le :
    (momentScalarGrow2622K02P119Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P119Expected]

end ConnesWeilRH.Dev
