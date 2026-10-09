import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P146 : ℚ := ((-796617302025302128077019145542189871611 : ℚ) / 18410343197234621243816919992316723200)

def momentPanelGrowth2622K05P146 : ℚ := ((35335170796783382497069512254791867405089 : ℚ) / 46219556018921906744674517427935825100800)

theorem momentPanelPhase_owner2622K05P146 :
    (momentPanelPhase2622K05P146 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (113 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P146, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P146 :
    (momentPanelGrowth2622K05P146 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (113 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P146, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P146Input : RatPair2542 := (momentPanelPhase2622K05P146 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P146Expected : RatState2542 :=
  ((((344853830380886128779483701594799898165641249811151639758236015699072900387613 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((109293655679166164580667765589 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K05P146_replay :
    compactExp2620 momentScalarAmp2622K05P146Input 20 = momentScalarAmp2622K05P146Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P146_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (113 / 200) 0) -
      (momentScalarAmp2622K05P146Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P146Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P146 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P146]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P146 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P146 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P146Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P146Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P146_replay] at h
  simpa only [momentPanelPhase_owner2622K05P146] using h

theorem momentScalarAmp2622K05P146_radius_le :
    (momentScalarAmp2622K05P146Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P146Expected]

def momentScalarGrow2622K05P146Input : RatPair2542 := (momentPanelGrowth2622K05P146 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P146Expected : RatState2542 :=
  ((((4587961372552009423949377022393878082135696518828849376954787940901820568292486732690481359277645 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5815927747399560363045871964960112612467843774663 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P146_replay :
    compactExp2620 momentScalarGrow2622K05P146Input 20 = momentScalarGrow2622K05P146Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P146_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (113 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P146Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P146Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P146 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P146]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P146 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P146 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P146Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P146Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P146_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P146] using h

theorem momentScalarGrow2622K05P146_radius_le :
    (momentScalarGrow2622K05P146Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P146Expected]

end ConnesWeilRH.Dev
