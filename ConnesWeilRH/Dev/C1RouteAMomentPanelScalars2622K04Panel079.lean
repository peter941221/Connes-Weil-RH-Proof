import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P079 : ℚ := ((-353767687277038378900355574795501599938968329869341453 : ℚ) / 11292098295151013386956946933090515620033014739763200)

def momentPanelGrowth2622K04P079 : ℚ := ((753689812726917360394229272040232805358713586439491269 : ℚ) / 4643057539590549105076203975458681515550673178774732800)

theorem momentPanelPhase_owner2622K04P079 :
    (momentPanelPhase2622K04P079 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-21 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P079, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P079 :
    (momentPanelGrowth2622K04P079 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-21 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P079, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P079Input : RatPair2542 := (momentPanelPhase2622K04P079 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P079Expected : RatState2542 :=
  ((((13231875850899939398933421320005722175528938804591130379642577471369625443023582895 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((16773896518992961866437370839614189 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K04P079_replay :
    compactExp2620 momentScalarAmp2622K04P079Input 20 = momentScalarAmp2622K04P079Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P079_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-21 / 200) 0) -
      (momentScalarAmp2622K04P079Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P079Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P079 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P079]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P079 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P079 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P079Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P079Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P079_replay] at h
  simpa only [momentPanelPhase_owner2622K04P079] using h

theorem momentScalarAmp2622K04P079_radius_le :
    (momentScalarAmp2622K04P079Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P079Expected]

def momentScalarGrow2622K04P079Input : RatPair2542 := (momentPanelGrowth2622K04P079 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P079Expected : RatState2542 :=
  ((((1256220808128105618822000181308388973010879425725968718642832155720448293202636012793281366747715 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3184897629843272759434305272591786237882641268029 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P079_replay :
    compactExp2620 momentScalarGrow2622K04P079Input 20 = momentScalarGrow2622K04P079Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P079_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-21 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P079Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P079Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P079 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P079]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P079 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P079 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P079Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P079Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P079_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P079] using h

theorem momentScalarGrow2622K04P079_radius_le :
    (momentScalarGrow2622K04P079Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P079Expected]

end ConnesWeilRH.Dev
