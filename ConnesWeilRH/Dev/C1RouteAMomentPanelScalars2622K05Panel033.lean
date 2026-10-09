import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P033 : ℚ := ((-825975466266831505838760957339090128389 : ℚ) / 18410343197234621243816919992316723200)

def momentPanelGrowth2622K05P033 : ℚ := ((35335170796783382497069512254791867405089 : ℚ) / 46219556018921906744674517427935825100800)

theorem momentPanelPhase_owner2622K05P033 :
    (momentPanelPhase2622K05P033 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-113 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P033, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P033 :
    (momentPanelGrowth2622K05P033 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-113 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P033, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P033Input : RatPair2542 := (momentPanelPhase2622K05P033 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P033Expected : RatState2542 :=
  ((((1093716537393442842029416798858057629225494184846276628313996272677734696741 : ℚ) / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384), 0), ((88739041694435042903085176927 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P033_replay :
    compactExp2620 momentScalarAmp2622K05P033Input 20 = momentScalarAmp2622K05P033Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P033_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-113 / 200) 0) -
      (momentScalarAmp2622K05P033Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P033Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P033 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P033]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P033 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P033 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P033Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P033Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P033_replay] at h
  simpa only [momentPanelPhase_owner2622K05P033] using h

theorem momentScalarAmp2622K05P033_radius_le :
    (momentScalarAmp2622K05P033Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P033Expected]

def momentScalarGrow2622K05P033Input : RatPair2542 := (momentPanelGrowth2622K05P033 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P033Expected : RatState2542 :=
  ((((4587961372552009423949377022393878082135696518828849376954787940901820568292486732690481359277645 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5815927747399560363045871964960112612467843774663 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P033_replay :
    compactExp2620 momentScalarGrow2622K05P033Input 20 = momentScalarGrow2622K05P033Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P033_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-113 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P033Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P033Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P033 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P033]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P033 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P033 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P033Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P033Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P033_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P033] using h

theorem momentScalarGrow2622K05P033_radius_le :
    (momentScalarGrow2622K05P033Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P033Expected]

end ConnesWeilRH.Dev
