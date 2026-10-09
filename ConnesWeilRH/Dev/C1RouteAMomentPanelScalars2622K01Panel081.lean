import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P081 : ℚ := ((-28559905058697941501528962549528783864209746386596917 : ℚ) / 944623885417439547278426568880148356014920853094400)

def momentPanelGrowth2622K01P081 : ℚ := ((199215363095292337026848561224509869192345855076807153 : ℚ) / 3510549804513104422532344927217172241373110501743001600)

theorem momentPanelPhase_owner2622K01P081 :
    (momentPanelPhase2622K01P081 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-17 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P081, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P081 :
    (momentPanelGrowth2622K01P081 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-17 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P081, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P081Input : RatPair2542 := (momentPanelPhase2622K01P081 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P081Expected : RatState2542 :=
  ((((158150980744264991730595168797022700588153002939566047118784587659017120166480649687 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((200485966305796090438756134473310265 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P081_replay :
    compactExp2620 momentScalarAmp2622K01P081Input 20 = momentScalarAmp2622K01P081Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P081_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-17 / 200) 0) -
      (momentScalarAmp2622K01P081Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P081Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P081 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P081]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P081 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P081 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P081Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P081Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P081_replay] at h
  simpa only [momentPanelPhase_owner2622K01P081] using h

theorem momentScalarAmp2622K01P081_radius_le :
    (momentScalarAmp2622K01P081Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P081Expected]

def momentScalarGrow2622K01P081Input : RatPair2542 := (momentPanelGrowth2622K01P081 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P081Expected : RatState2542 :=
  ((((1130352234364373673987481121948170395137843858037259925759451259576414001470885011269594627716519 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2865783221630020654085526972057982818040286326987 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P081_replay :
    compactExp2620 momentScalarGrow2622K01P081Input 20 = momentScalarGrow2622K01P081Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P081_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-17 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P081Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P081Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P081 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P081]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P081 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P081 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P081Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P081Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P081_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P081] using h

theorem momentScalarGrow2622K01P081_radius_le :
    (momentScalarGrow2622K01P081Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P081Expected]

end ConnesWeilRH.Dev
