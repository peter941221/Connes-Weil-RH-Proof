import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K15
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K15P164 : ℚ := ((-797411396102792880599277954212437592727 : ℚ) / 12033553617846536062527904187993292800)

def momentPanelGrowth2622K15P164 : ℚ := ((117596307518889946669138124795355241 : ℚ) / 49691903528946592538670765650739200)

theorem momentPanelPhase_owner2622K15P164 :
    (momentPanelPhase2622K15P164 : ℝ) = momentPhase2619 ((capturedNodes2584 15).re * (storedWidth 15 ^ 2)) (149 / 200) 0 := by
  norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentPanelPhase2622K15P164, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K15P164 :
    (momentPanelGrowth2622K15P164 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 15).re * (storedWidth 15 ^ 2))
      (149 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentPanelGrowth2622K15P164, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K15P164Input : RatPair2542 := (momentPanelPhase2622K15P164 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K15P164Expected : RatState2542 :=
  ((((35545717722906759830243200104873545344534367698702910840400399856219 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417896701627352074451229 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K15P164_replay :
    compactExp2620 momentScalarAmp2622K15P164Input 20 = momentScalarAmp2622K15P164Expected := by
  decide +kernel

theorem momentScalarAmp2622K15P164_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 15).re * (storedWidth 15 ^ 2)) (149 / 200) 0) -
      (momentScalarAmp2622K15P164Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K15P164Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K15P164 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentPanelPhase2622K15P164]
  have h := compactExp_real_error2620 momentPanelPhase2622K15P164 20 hsmall
  change |Real.exp (momentPanelPhase2622K15P164 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K15P164Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K15P164Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K15P164_replay] at h
  simpa only [momentPanelPhase_owner2622K15P164] using h

theorem momentScalarAmp2622K15P164_radius_le :
    (momentScalarAmp2622K15P164Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentScalarAmp2622K15P164Expected]

def momentScalarGrow2622K15P164Input : RatPair2542 := (momentPanelGrowth2622K15P164 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K15P164Expected : RatState2542 :=
  ((((5692462314873791237125758725578247447704528061297228713793284314124335509652508358303794210373355 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((28864147937963046266178811953849203442862838849631 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K15P164_replay :
    compactExp2620 momentScalarGrow2622K15P164Input 20 = momentScalarGrow2622K15P164Expected := by
  decide +kernel

theorem momentScalarGrow2622K15P164_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 15).re * (storedWidth 15 ^ 2)) (149 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K15P164Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K15P164Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K15P164 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentPanelGrowth2622K15P164]
  have h := compactExp_real_error2620 momentPanelGrowth2622K15P164 20 hsmall
  change |Real.exp (momentPanelGrowth2622K15P164 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K15P164Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K15P164Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K15P164_replay] at h
  simpa only [momentPanelGrowth_owner2622K15P164] using h

theorem momentScalarGrow2622K15P164_radius_le :
    (momentScalarGrow2622K15P164Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentScalarGrow2622K15P164Expected]

end ConnesWeilRH.Dev
