import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P145 : ℚ := ((-301013407797219765920858545338763149392881843459179537 : ℚ) / 7900957777281652709562459469678515175987608761139200)

def momentPanelGrowth2622K04P145 : ℚ := ((7073372691851068996936005527718970113124808832095869 : ℚ) / 8755736420443252082328266936781817813167235714252800)

theorem momentPanelPhase_owner2622K04P145 :
    (momentPanelPhase2622K04P145 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (111 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P145, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P145 :
    (momentPanelGrowth2622K04P145 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (111 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P145, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P145Input : RatPair2542 := (momentPanelPhase2622K04P145 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P145Expected : RatState2542 :=
  ((((30385614395666507215431477681311982774960233904354778317581123995663452170154911 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((19259871532065369971272188605579 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K04P145_replay :
    compactExp2620 momentScalarAmp2622K04P145Input 20 = momentScalarAmp2622K04P145Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P145_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (111 / 200) 0) -
      (momentScalarAmp2622K04P145Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P145Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P145 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P145]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P145 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P145 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P145Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P145Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P145_replay] at h
  simpa only [momentPanelPhase_owner2622K04P145] using h

theorem momentScalarAmp2622K04P145_radius_le :
    (momentScalarAmp2622K04P145Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P145Expected]

def momentScalarGrow2622K04P145Input : RatPair2542 := (momentPanelGrowth2622K04P145 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P145Expected : RatState2542 :=
  ((((4791218098063438655540939603789778600547626631352769028471859853338765174111074290537791206965451 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((6073585818551724810481655742812158104918799407855 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P145_replay :
    compactExp2620 momentScalarGrow2622K04P145Input 20 = momentScalarGrow2622K04P145Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P145_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (111 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P145Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P145Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P145 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P145]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P145 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P145 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P145Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P145Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P145_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P145] using h

theorem momentScalarGrow2622K04P145_radius_le :
    (momentScalarGrow2622K04P145Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P145Expected]

end ConnesWeilRH.Dev
