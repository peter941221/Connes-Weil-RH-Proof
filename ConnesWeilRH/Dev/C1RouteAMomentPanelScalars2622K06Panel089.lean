import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P089 : ℚ := ((-20013333 : ℚ) / 666650)

def momentPanelGrowth2622K06P089 : ℚ := ((38326667 : ℚ) / 833166675)

theorem momentPanelPhase_owner2622K06P089 :
    (momentPanelPhase2622K06P089 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-1 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P089, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P089 :
    (momentPanelGrowth2622K06P089 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (-1 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P089, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P089Input : RatPair2542 := (momentPanelPhase2622K06P089 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P089Expected : RatState2542 :=
  ((((195772883150663454729550020180010436806689339814377457385497855200586809062150808829 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((248178718096283883126531737413156843 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P089_replay :
    compactExp2620 momentScalarAmp2622K06P089Input 20 = momentScalarAmp2622K06P089Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P089_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-1 / 200) 0) -
      (momentScalarAmp2622K06P089Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P089Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P089 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P089]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P089 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P089 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P089Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P089Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P089_replay] at h
  simpa only [momentPanelPhase_owner2622K06P089] using h

theorem momentScalarAmp2622K06P089_radius_le :
    (momentScalarAmp2622K06P089Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P089Expected]

def momentScalarGrow2622K06P089Input : RatPair2542 := (momentPanelGrowth2622K06P089 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P089Expected : RatState2542 :=
  ((((1118270025848811644440609730620753464344166110719014447274223254113712580419932086251337869541885 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2835151214590418404947539007840128158435241371647 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P089_replay :
    compactExp2620 momentScalarGrow2622K06P089Input 20 = momentScalarGrow2622K06P089Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P089_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (-1 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P089Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P089Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P089 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P089]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P089 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P089 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P089Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P089Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P089_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P089] using h

theorem momentScalarGrow2622K06P089_radius_le :
    (momentScalarGrow2622K06P089Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P089Expected]

end ConnesWeilRH.Dev
