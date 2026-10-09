import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P178 : ℚ := ((-333583730916309851841023286027188220929651165563734207 : ℚ) / 2475132948690675625731279528219314465514959195340800)

def momentPanelGrowth2622K02P178 : ℚ := ((2548907980215543273008414713816769030353083578586886213 : ℚ) / 205630283152303358075508233562645176925803305028812800)

theorem momentPanelPhase_owner2622K02P178 :
    (momentPanelPhase2622K02P178 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (177 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P178, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P178 :
    (momentPanelGrowth2622K02P178 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (177 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P178, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P178Input : RatPair2542 := (momentPanelPhase2622K02P178 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P178Expected : RatState2542 :=
  ((((31400425395305842250270609795603799637 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P178_replay :
    compactExp2620 momentScalarAmp2622K02P178Input 20 = momentScalarAmp2622K02P178Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P178_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (177 / 200) 0) -
      (momentScalarAmp2622K02P178Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P178Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P178 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P178]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P178 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P178 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P178Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P178Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P178_replay] at h
  simpa only [momentPanelPhase_owner2622K02P178] using h

theorem momentScalarAmp2622K02P178_radius_le :
    (momentScalarAmp2622K02P178Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P178Expected]

def momentScalarGrow2622K02P178Input : RatPair2542 := (momentPanelGrowth2622K02P178 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P178Expected : RatState2542 :=
  ((((258168631429636513952785885310512216171248834779972004491532179600036126722949406141950847916943964735 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((163631875934409633798455762095248101819040550261929793 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K02P178_replay :
    compactExp2620 momentScalarGrow2622K02P178Input 20 = momentScalarGrow2622K02P178Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P178_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (177 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P178Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P178Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P178 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P178]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P178 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P178 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P178Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P178Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P178_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P178] using h

theorem momentScalarGrow2622K02P178_radius_le :
    (momentScalarGrow2622K02P178Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 66 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P178Expected]

end ConnesWeilRH.Dev
