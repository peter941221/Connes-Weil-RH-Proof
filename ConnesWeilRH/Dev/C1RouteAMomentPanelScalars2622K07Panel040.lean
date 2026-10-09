import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P040 : ℚ := ((-107146960178323523108393539550430733575 : ℚ) / 2450033950482707180531132166345588736)

def momentPanelGrowth2622K07P040 : ℚ := ((373644172311239357913058643167381 : ℚ) / 608472288109550112718417538580480)

theorem momentPanelPhase_owner2622K07P040 :
    (momentPanelPhase2622K07P040 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-99 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P040, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P040 :
    (momentPanelGrowth2622K07P040 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-99 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P040, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P040Input : RatPair2542 := (momentPanelPhase2622K07P040 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P040Expected : RatState2542 :=
  ((((108551152227633271419769353296967365779285534192633450646025995641785613448719 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((275223762793131051661043335577 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P040_replay :
    compactExp2620 momentScalarAmp2622K07P040Input 20 = momentScalarAmp2622K07P040Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P040_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-99 / 200) 0) -
      (momentScalarAmp2622K07P040Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P040Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P040 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P040]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P040 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P040 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P040Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P040Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P040_replay] at h
  simpa only [momentPanelPhase_owner2622K07P040] using h

theorem momentScalarAmp2622K07P040_radius_le :
    (momentScalarAmp2622K07P040Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P040Expected]

def momentScalarGrow2622K07P040Input : RatPair2542 := (momentPanelGrowth2622K07P040 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P040Expected : RatState2542 :=
  ((((3947167310587378961068926107080866868484657634705869172002899007262672408489339762801023823996919 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5003626080232207642476121648195560106355125959931 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P040_replay :
    compactExp2620 momentScalarGrow2622K07P040Input 20 = momentScalarGrow2622K07P040Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P040_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-99 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P040Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P040Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P040 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P040]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P040 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P040 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P040Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P040Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P040_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P040] using h

theorem momentScalarGrow2622K07P040_radius_le :
    (momentScalarGrow2622K07P040Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P040Expected]

end ConnesWeilRH.Dev
