import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P119 : ℚ := ((-801017931134216341130077023362663892577 : ℚ) / 24689777210525178407070988990467276800)

def momentPanelGrowth2622K05P119 : ℚ := ((1943928476428133899760917396944798009 : ℚ) / 8397931696391974139035359394974924800)

theorem momentPanelPhase_owner2622K05P119 :
    (momentPanelPhase2622K05P119 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (59 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P119, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P119 :
    (momentPanelGrowth2622K05P119 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (59 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P119, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P119Input : RatPair2542 := (momentPanelPhase2622K05P119 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P119Expected : RatState2542 :=
  ((((1085253062075197607824334615990915191416223010360356696883695345235885809004036075 : ℚ) / 133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536), 0), ((5503057046611265988053442527374393 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K05P119_replay :
    compactExp2620 momentScalarAmp2622K05P119Input 20 = momentScalarAmp2622K05P119Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P119_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (59 / 200) 0) -
      (momentScalarAmp2622K05P119Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P119Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P119 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P119]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P119 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P119 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P119Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P119Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P119_replay] at h
  simpa only [momentPanelPhase_owner2622K05P119] using h

theorem momentScalarAmp2622K05P119_radius_le :
    (momentScalarAmp2622K05P119Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P119Expected]

def momentScalarGrow2622K05P119Input : RatPair2542 := (momentPanelGrowth2622K05P119 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P119Expected : RatState2542 :=
  ((((1346163538841215779844206294439103957614655352705032620660401998051709326554383129417621365817803 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3412929282617931405492018237402461098448282533611 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P119_replay :
    compactExp2620 momentScalarGrow2622K05P119Input 20 = momentScalarGrow2622K05P119Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P119_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (59 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P119Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P119Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P119 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P119]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P119 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P119 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P119Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P119Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P119_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P119] using h

theorem momentScalarGrow2622K05P119_radius_le :
    (momentScalarGrow2622K05P119Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P119Expected]

end ConnesWeilRH.Dev
