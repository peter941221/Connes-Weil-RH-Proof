import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P078 : ℚ := ((-33442918871585758219572332892620461825 : ℚ) / 1067422652620980111071495940680450048)

def momentPanelGrowth2622K07P078 : ℚ := ((37244056098544548623160232115118675 : ℚ) / 240508813080101507887166505749577728)

theorem momentPanelPhase_owner2622K07P078 :
    (momentPanelPhase2622K07P078 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-23 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P078, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P078 :
    (momentPanelGrowth2622K07P078 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-23 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P078, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P078Input : RatPair2542 := (momentPanelPhase2622K07P078 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P078Expected : RatState2542 :=
  ((((52835002968938495342491900136738667325708392340645357692135816122498932405751537407 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((33489162226376997427453015747977141 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P078_replay :
    compactExp2620 momentScalarAmp2622K07P078Input 20 = momentScalarAmp2622K07P078Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P078_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-23 / 200) 0) -
      (momentScalarAmp2622K07P078Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P078Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P078 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P078]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P078 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P078 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P078Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P078Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P078_replay] at h
  simpa only [momentPanelPhase_owner2622K07P078] using h

theorem momentScalarAmp2622K07P078_radius_le :
    (momentScalarAmp2622K07P078Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P078Expected]

def momentScalarGrow2622K07P078Input : RatPair2542 := (momentPanelGrowth2622K07P078 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P078Expected : RatState2542 :=
  ((((2493741310724962588539738723613524367596777970332567368093632375401084973094975396571675956959281 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3161192202504823050527049490111453277892992546391 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P078_replay :
    compactExp2620 momentScalarGrow2622K07P078Input 20 = momentScalarGrow2622K07P078Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P078_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-23 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P078Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P078Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P078 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P078]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P078 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P078 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P078Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P078Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P078_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P078] using h

theorem momentScalarGrow2622K07P078_radius_le :
    (momentScalarGrow2622K07P078Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P078Expected]

end ConnesWeilRH.Dev
