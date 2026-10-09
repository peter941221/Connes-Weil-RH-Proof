import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P146 : ℚ := ((-18974299 : ℚ) / 453850)

def momentPanelGrowth2622K06P146 : ℚ := ((900576001 : ℚ) / 1139400025)

theorem momentPanelPhase_owner2622K06P146 :
    (momentPanelPhase2622K06P146 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (113 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P146, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P146 :
    (momentPanelGrowth2622K06P146 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (113 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P146, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P146Input : RatPair2542 := (momentPanelPhase2622K06P146 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P146Expected : RatState2542 :=
  ((((372224916598047006321160360330145358514939331993880205299955183437688711893091 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1887482227209591015421613733377 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P146_replay :
    compactExp2620 momentScalarAmp2622K06P146Input 20 = momentScalarAmp2622K06P146Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P146_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (113 / 200) 0) -
      (momentScalarAmp2622K06P146Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P146Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P146 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P146]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P146 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P146 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P146Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P146Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P146_replay] at h
  simpa only [momentPanelPhase_owner2622K06P146] using h

theorem momentScalarAmp2622K06P146_radius_le :
    (momentScalarAmp2622K06P146Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P146Expected]

def momentScalarGrow2622K06P146Input : RatPair2542 := (momentPanelGrowth2622K06P146 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P146Expected : RatState2542 :=
  ((((4708285269182928461200281617497124717171537686295696173119378493865080509722356597988199283223051 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((5968456148624820688116076670341546511435363153587 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P146_replay :
    compactExp2620 momentScalarGrow2622K06P146Input 20 = momentScalarGrow2622K06P146Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P146_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (113 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P146Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P146Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P146 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P146]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P146 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P146 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P146Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P146Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P146_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P146] using h

theorem momentScalarGrow2622K06P146_radius_le :
    (momentScalarGrow2622K06P146Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P146Expected]

end ConnesWeilRH.Dev
