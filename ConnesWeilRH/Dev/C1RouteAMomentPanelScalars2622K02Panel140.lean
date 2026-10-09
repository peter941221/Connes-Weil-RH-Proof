import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P140 : ℚ := ((-108325722149686132193942485726854629796115337566963793 : ℚ) / 2835370266329659899710390906908367037937964443238400)

def momentPanelGrowth2622K02P140 : ℚ := ((4686828668038655682249558531197248719829076026093768479 : ℚ) / 7813496181397400758647195811299247058979587686295142400)

theorem momentPanelPhase_owner2622K02P140 :
    (momentPanelPhase2622K02P140 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (101 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P140, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P140 :
    (momentPanelGrowth2622K02P140 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (101 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P140, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P140Input : RatPair2542 := (momentPanelPhase2622K02P140 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P140Expected : RatState2542 :=
  ((((54615572569362158542302774501885792728413089485868330029760482934586492961745981 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((69235988352555776514809276044049 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P140_replay :
    compactExp2620 momentScalarAmp2622K02P140Input 20 = momentScalarAmp2622K02P140Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P140_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (101 / 200) 0) -
      (momentScalarAmp2622K02P140Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P140Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P140 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P140]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P140 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P140 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P140Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P140Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P140_replay] at h
  simpa only [momentPanelPhase_owner2622K02P140] using h

theorem momentScalarAmp2622K02P140_radius_le :
    (momentScalarAmp2622K02P140Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P140Expected]

def momentScalarGrow2622K02P140Input : RatPair2542 := (momentPanelGrowth2622K02P140 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P140Expected : RatState2542 :=
  ((((1945695029105780775162951611113254042734324058913939311855612557581341053694890157390230063993895 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1233230030284445245864277998605399264500552523747 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K02P140_replay :
    compactExp2620 momentScalarGrow2622K02P140Input 20 = momentScalarGrow2622K02P140Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P140_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (101 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P140Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P140Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P140 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P140]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P140 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P140 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P140Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P140Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P140_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P140] using h

theorem momentScalarGrow2622K02P140_radius_le :
    (momentScalarGrow2622K02P140Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P140Expected]

end ConnesWeilRH.Dev
