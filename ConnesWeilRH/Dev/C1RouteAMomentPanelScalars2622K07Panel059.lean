import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P059 : ℚ := ((-34867764865074422814548179211936463475 : ℚ) / 981100717347838601747176439207165952)

def momentPanelGrowth2622K07P059 : ℚ := ((340696012757237791403329308231688530025 : ℚ) / 1104762852655037287445368765559523508224)

theorem momentPanelPhase_owner2622K07P059 :
    (momentPanelPhase2622K07P059 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-61 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P059, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P059 :
    (momentPanelGrowth2622K07P059 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-61 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P059, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P059Input : RatPair2542 := (momentPanelPhase2622K07P059 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P059Expected : RatState2542 :=
  ((((196317152801813678929302204105570408113727942169878164827718882774419644516546049 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((995479968031696033780865283775185 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P059_replay :
    compactExp2620 momentScalarAmp2622K07P059Input 20 = momentScalarAmp2622K07P059Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P059_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-61 / 200) 0) -
      (momentScalarAmp2622K07P059Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P059Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P059 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P059]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P059 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P059 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P059Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P059Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P059_replay] at h
  simpa only [momentPanelPhase_owner2622K07P059] using h

theorem momentScalarAmp2622K07P059_radius_le :
    (momentScalarAmp2622K07P059Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P059Expected]

def momentScalarGrow2622K07P059Input : RatPair2542 := (momentPanelGrowth2622K07P059 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P059Expected : RatState2542 :=
  ((((2907568658461263611634333599210792622288436466174434984860816602233379867896153700514450026644429 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3685780071107516606116920748290864215698371166925 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P059_replay :
    compactExp2620 momentScalarGrow2622K07P059Input 20 = momentScalarGrow2622K07P059Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P059_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-61 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P059Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P059Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P059 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P059]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P059 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P059 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P059Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P059Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P059_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P059] using h

theorem momentScalarGrow2622K07P059_radius_le :
    (momentScalarGrow2622K07P059Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P059Expected]

end ConnesWeilRH.Dev
