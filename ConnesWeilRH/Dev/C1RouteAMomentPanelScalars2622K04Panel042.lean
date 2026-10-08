import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P042 : ℚ := ((-1019498317495372354054821344344178501238540640261369 : ℚ) / 23578131883502457235082884215305659653042974228480)

def momentPanelGrowth2622K04P042 : ℚ := ((19183604216890685009541860514917564505780969024185247 : ℚ) / 33020945343214358404152610017780464424864864167526400)

theorem momentPanelPhase_owner2622K04P042 :
    (momentPanelPhase2622K04P042 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-19 / 40) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P042, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P042 :
    (momentPanelGrowth2622K04P042 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-19 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P042, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P042Input : RatPair2542 := (momentPanelPhase2622K04P042 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P042Expected : RatState2542 :=
  ((((355693180877479326055431304373181301485047756098738555405608421428130077616035 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((225457842796588663481569007873 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K04P042_replay :
    compactExp2620 momentScalarAmp2622K04P042Input 20 = momentScalarAmp2622K04P042Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P042_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-19 / 40) 0) -
      (momentScalarAmp2622K04P042Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P042Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P042 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P042]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P042 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P042 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P042Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P042Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P042_replay] at h
  simpa only [momentPanelPhase_owner2622K04P042] using h

theorem momentScalarAmp2622K04P042_radius_le :
    (momentScalarAmp2622K04P042Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P042Expected]

def momentScalarGrow2622K04P042Input : RatPair2542 := (momentPanelGrowth2622K04P042 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P042Expected : RatState2542 :=
  ((((954647702601806942241759840561535818928336771314625220646823901475234710286785855122127846117365 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((4840636250933912506478919368513893154720904525317 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P042_replay :
    compactExp2620 momentScalarGrow2622K04P042Input 20 = momentScalarGrow2622K04P042Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P042_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-19 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P042Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P042Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P042 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P042]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P042 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P042 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P042Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P042Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P042_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P042] using h

theorem momentScalarGrow2622K04P042_radius_le :
    (momentScalarGrow2622K04P042Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P042Expected]

end ConnesWeilRH.Dev
