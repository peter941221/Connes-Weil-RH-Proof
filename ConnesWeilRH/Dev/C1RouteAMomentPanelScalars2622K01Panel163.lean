import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P163 : ℚ := ((-85455239212789631536500284297716532999278256435218779 : ℚ) / 1312425615827765408627146863207283252660754658099200)

def momentPanelGrowth2622K01P163 : ℚ := ((33033432572518810052895720370764916345624397942695651 : ℚ) / 15213996548745402895119984491391547067920754619187200)

theorem momentPanelPhase_owner2622K01P163 :
    (momentPanelPhase2622K01P163 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (147 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P163, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P163 :
    (momentPanelGrowth2622K01P163 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (147 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P163, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P163Input : RatPair2542 := (momentPanelPhase2622K01P163 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P163Expected : RatState2542 :=
  ((((56311040372503631833753672069589569479128666757255229441816617733079 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417994413542996683282225 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P163_replay :
    compactExp2620 momentScalarAmp2622K01P163Input 20 = momentScalarAmp2622K01P163Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P163_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (147 / 200) 0) -
      (momentScalarAmp2622K01P163Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P163Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P163 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P163]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P163 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P163 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P163Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P163Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P163_replay] at h
  simpa only [momentPanelPhase_owner2622K01P163] using h

theorem momentScalarAmp2622K01P163_radius_le :
    (momentScalarAmp2622K01P163Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P163Expected]

def momentScalarGrow2622K01P163Input : RatPair2542 := (momentPanelGrowth2622K01P163 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P163Expected : RatState2542 :=
  ((((18731032671808081037463890479865800280613516612620274827328890899077852001686024226568493520609785 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5936088910645779558909887603629122100898866121389 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K01P163_replay :
    compactExp2620 momentScalarGrow2622K01P163Input 20 = momentScalarGrow2622K01P163Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P163_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (147 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P163Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P163Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P163 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P163]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P163 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P163 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P163Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P163Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P163_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P163] using h

theorem momentScalarGrow2622K01P163_radius_le :
    (momentScalarGrow2622K01P163Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P163Expected]

end ConnesWeilRH.Dev
