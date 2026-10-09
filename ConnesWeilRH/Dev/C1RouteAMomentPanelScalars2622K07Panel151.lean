import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P151 : ℚ := ((-87336779353112373854525979535873067025 : ℚ) / 2017775237009682780455968346938015744)

def momentPanelGrowth2622K07P151 : ℚ := ((34023402872708498621483308150261555025 : ℚ) / 32026208717900438722798645042137268224)

theorem momentPanelPhase_owner2622K07P151 :
    (momentPanelPhase2622K07P151 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (123 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P151, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P151 :
    (momentPanelGrowth2622K07P151 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (123 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P151, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P151Input : RatPair2542 := (momentPanelPhase2622K07P151 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P151Expected : RatState2542 :=
  ((((42524211892920551666090929097852297224175316195976038850370411109442318162415 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((431266961303159743392303322671 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P151_replay :
    compactExp2620 momentScalarAmp2622K07P151Input 20 = momentScalarAmp2622K07P151Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P151_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (123 / 200) 0) -
      (momentScalarAmp2622K07P151Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P151Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P151 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P151]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P151 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P151 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P151Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P151Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P151_replay] at h
  simpa only [momentPanelPhase_owner2622K07P151] using h

theorem momentScalarAmp2622K07P151_radius_le :
    (momentScalarAmp2622K07P151Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P151Expected]

def momentScalarGrow2622K07P151Input : RatPair2542 := (momentPanelGrowth2622K07P151 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P151Expected : RatState2542 :=
  ((((6179825864675034483992447980440523742542582585615049999716681867564248209708383937207005225578065 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7833852029816429524406238755932797058262680632555 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P151_replay :
    compactExp2620 momentScalarGrow2622K07P151Input 20 = momentScalarGrow2622K07P151Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P151_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (123 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P151Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P151Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P151 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P151]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P151 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P151 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P151Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P151Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P151_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P151] using h

theorem momentScalarGrow2622K07P151_radius_le :
    (momentScalarGrow2622K07P151Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P151Expected]

end ConnesWeilRH.Dev
