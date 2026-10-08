import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P034 : ℚ := ((-384065484701640976987118719996994516070836536060820463 : ℚ) / 7900957777281652709562459469678515175987608761139200)

def momentPanelGrowth2622K04P034 : ℚ := ((7073372691851068996936005527718970113124808832095869 : ℚ) / 8755736420443252082328266936781817813167235714252800)

theorem momentPanelPhase_owner2622K04P034 :
    (momentPanelPhase2622K04P034 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-111 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P034, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P034 :
    (momentPanelGrowth2622K04P034 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-111 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P034, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P034Input : RatPair2542 := (momentPanelPhase2622K04P034 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P034Expected : RatState2542 :=
  ((((827023510856177413877884505257079461048440161006124888830271242085679409615 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1049634377644470626465751419 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P034_replay :
    compactExp2620 momentScalarAmp2622K04P034Input 20 = momentScalarAmp2622K04P034Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P034_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-111 / 200) 0) -
      (momentScalarAmp2622K04P034Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P034Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P034 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P034]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P034 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P034 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P034Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P034Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P034_replay] at h
  simpa only [momentPanelPhase_owner2622K04P034] using h

theorem momentScalarAmp2622K04P034_radius_le :
    (momentScalarAmp2622K04P034Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 93 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P034Expected]

def momentScalarGrow2622K04P034Input : RatPair2542 := (momentPanelGrowth2622K04P034 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P034Expected : RatState2542 :=
  ((((4791218098063438655540939603789778600547626631352769028471859853338765174111074290537791206965451 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((6073585818551724810481655742812158104918799407855 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P034_replay :
    compactExp2620 momentScalarGrow2622K04P034Input 20 = momentScalarGrow2622K04P034Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P034_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-111 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P034Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P034Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P034 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P034]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P034 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P034 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P034Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P034Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P034_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P034] using h

theorem momentScalarGrow2622K04P034_radius_le :
    (momentScalarGrow2622K04P034Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P034Expected]

end ConnesWeilRH.Dev
