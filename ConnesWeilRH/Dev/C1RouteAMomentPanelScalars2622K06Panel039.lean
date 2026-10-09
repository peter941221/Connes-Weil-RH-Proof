import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P039 : ℚ := ((-21003233 : ℚ) / 496650)

def momentPanelGrowth2622K06P039 : ℚ := ((819745201 : ℚ) / 1368630025)

theorem momentPanelPhase_owner2622K06P039 :
    (momentPanelPhase2622K06P039 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-101 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P039, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P039 :
    (momentPanelGrowth2622K06P039 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-101 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P039, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P039Input : RatPair2542 := (momentPanelPhase2622K06P039 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P039Expected : RatState2542 :=
  ((((919112097822367605720980263356259633292813624728796470776553808502243231572547 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((72822650694235866061427500849 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622K06P039_replay :
    compactExp2620 momentScalarAmp2622K06P039Input 20 = momentScalarAmp2622K06P039Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P039_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-101 / 200) 0) -
      (momentScalarAmp2622K06P039Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P039Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P039 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P039]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P039 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P039 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P039Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P039Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P039_replay] at h
  simpa only [momentPanelPhase_owner2622K06P039] using h

theorem momentScalarAmp2622K06P039_radius_le :
    (momentScalarAmp2622K06P039Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P039Expected]

def momentScalarGrow2622K06P039Input : RatPair2542 := (momentPanelGrowth2622K06P039 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P039Expected : RatState2542 :=
  ((((1943974861605453911060208800500443510432011714576863925414895668898988393728306549333281766266491 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4928558985061274143812882618654721352353901382037 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P039_replay :
    compactExp2620 momentScalarGrow2622K06P039Input 20 = momentScalarGrow2622K06P039Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P039_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-101 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P039Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P039Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P039 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P039]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P039 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P039 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P039Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P039Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P039_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P039] using h

theorem momentScalarGrow2622K06P039_radius_le :
    (momentScalarGrow2622K06P039Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P039Expected]

end ConnesWeilRH.Dev
