import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K23
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K23P035 : ℚ := ((-827343242101657173250054748972331796433 : ℚ) / 19010702521502710688365758630382796800)

def momentPanelGrowth2622K23P035 : ℚ := ((18256062144143389676763564567284309443 : ℚ) / 26313384099297494624507966455912857600)

theorem momentPanelPhase_owner2622K23P035 :
    (momentPanelPhase2622K23P035 : ℝ) = momentPhase2619 ((capturedNodes2584 23).re * (storedWidth 23 ^ 2)) (-109 / 200) 0 := by
  norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentPanelPhase2622K23P035, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K23P035 :
    (momentPanelGrowth2622K23P035 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 23).re * (storedWidth 23 ^ 2))
      (-109 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentPanelGrowth2622K23P035, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K23P035Input : RatPair2542 := (momentPanelPhase2622K23P035 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K23P035Expected : RatState2542 :=
  ((((268633762302447353744865915553837084192460520983887700542956152865557588284649 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((85137575401698426107798657981 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K23P035_replay :
    compactExp2620 momentScalarAmp2622K23P035Input 20 = momentScalarAmp2622K23P035Expected := by
  decide +kernel

theorem momentScalarAmp2622K23P035_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 23).re * (storedWidth 23 ^ 2)) (-109 / 200) 0) -
      (momentScalarAmp2622K23P035Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K23P035Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K23P035 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentPanelPhase2622K23P035]
  have h := compactExp_real_error2620 momentPanelPhase2622K23P035 20 hsmall
  change |Real.exp (momentPanelPhase2622K23P035 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K23P035Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K23P035Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K23P035_replay] at h
  simpa only [momentPanelPhase_owner2622K23P035] using h

theorem momentScalarAmp2622K23P035_radius_le :
    (momentScalarAmp2622K23P035Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentScalarAmp2622K23P035Expected]

def momentScalarGrow2622K23P035Input : RatPair2542 := (momentPanelGrowth2622K23P035 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K23P035Expected : RatState2542 :=
  ((((4274737208978319746441751177034573736271641883928357062196486434045199901271999809317491992502291 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5418869603365138357168890170795796708692559936083 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K23P035_replay :
    compactExp2620 momentScalarGrow2622K23P035Input 20 = momentScalarGrow2622K23P035Expected := by
  decide +kernel

theorem momentScalarGrow2622K23P035_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 23).re * (storedWidth 23 ^ 2)) (-109 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K23P035Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K23P035Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K23P035 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentPanelGrowth2622K23P035]
  have h := compactExp_real_error2620 momentPanelGrowth2622K23P035 20 hsmall
  change |Real.exp (momentPanelGrowth2622K23P035 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K23P035Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K23P035Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K23P035_replay] at h
  simpa only [momentPanelGrowth_owner2622K23P035] using h

theorem momentScalarGrow2622K23P035_radius_le :
    (momentScalarGrow2622K23P035Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, momentScalarGrow2622K23P035Expected]

end ConnesWeilRH.Dev
