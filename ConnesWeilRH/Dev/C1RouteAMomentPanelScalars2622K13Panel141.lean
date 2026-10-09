import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K13
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K13P141 : ℚ := ((-795446896557507615365558410981119430421 : ℚ) / 19870676688697541514341122084909875200)

def momentPanelGrowth2622K13P141 : ℚ := ((660739174359222232834477654665694627 : ℚ) / 1098292480037737953456743657137766400)

theorem momentPanelPhase_owner2622K13P141 :
    (momentPanelPhase2622K13P141 : ℝ) = momentPhase2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2)) (103 / 200) 0 := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelPhase2622K13P141, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K13P141 :
    (momentPanelGrowth2622K13P141 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2))
      (103 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelGrowth2622K13P141, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K13P141Input : RatPair2542 := (momentPanelPhase2622K13P141 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K13P141Expected : RatState2542 :=
  ((((8795738783772704156518098447886222989051342545979247603550610737523315543197189 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((11150351642195077630262917237449 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K13P141_replay :
    compactExp2620 momentScalarAmp2622K13P141Input 20 = momentScalarAmp2622K13P141Expected := by
  decide +kernel

theorem momentScalarAmp2622K13P141_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2)) (103 / 200) 0) -
      (momentScalarAmp2622K13P141Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K13P141Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K13P141 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelPhase2622K13P141]
  have h := compactExp_real_error2620 momentPanelPhase2622K13P141 20 hsmall
  change |Real.exp (momentPanelPhase2622K13P141 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K13P141Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K13P141Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K13P141_replay] at h
  simpa only [momentPanelPhase_owner2622K13P141] using h

theorem momentScalarAmp2622K13P141_radius_le :
    (momentScalarAmp2622K13P141Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentScalarAmp2622K13P141Expected]

def momentScalarGrow2622K13P141Input : RatPair2542 := (momentPanelGrowth2622K13P141 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K13P141Expected : RatState2542 :=
  ((((3898277136682950579838848746325044994876914995281749355585538623369199761836510934195656659112051 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1235412629242076023704218738980822140214150384161 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K13P141_replay :
    compactExp2620 momentScalarGrow2622K13P141Input 20 = momentScalarGrow2622K13P141Expected := by
  decide +kernel

theorem momentScalarGrow2622K13P141_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2)) (103 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K13P141Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K13P141Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K13P141 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelGrowth2622K13P141]
  have h := compactExp_real_error2620 momentPanelGrowth2622K13P141 20 hsmall
  change |Real.exp (momentPanelGrowth2622K13P141 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K13P141Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K13P141Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K13P141_replay] at h
  simpa only [momentPanelGrowth_owner2622K13P141] using h

theorem momentScalarGrow2622K13P141_radius_le :
    (momentScalarGrow2622K13P141Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentScalarGrow2622K13P141Expected]

end ConnesWeilRH.Dev
