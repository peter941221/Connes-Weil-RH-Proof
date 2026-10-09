import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K15
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K15P119 : ℚ := ((-800015723697686702084183190018319426617 : ℚ) / 24689777210525178407070988990467276800)

def momentPanelGrowth2622K15P119 : ℚ := ((1955484030442369267752383414297060689 : ℚ) / 8397931696391974139035359394974924800)

theorem momentPanelPhase_owner2622K15P119 :
    (momentPanelPhase2622K15P119 : ℝ) = momentPhase2619 ((capturedNodes2584 15).re * (storedWidth 15 ^ 2)) (59 / 200) 0 := by
  norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentPanelPhase2622K15P119, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K15P119 :
    (momentPanelGrowth2622K15P119 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 15).re * (storedWidth 15 ^ 2))
      (59 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentPanelGrowth2622K15P119, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K15P119Input : RatPair2542 := (momentPanelPhase2622K15P119 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K15P119Expected : RatState2542 :=
  ((((18083391475320092448728728408114274535737840200822660035220415968649571439358477953 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((22924130442403160857173344680571023 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K15P119_replay :
    compactExp2620 momentScalarAmp2622K15P119Input 20 = momentScalarAmp2622K15P119Expected := by
  decide +kernel

theorem momentScalarAmp2622K15P119_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 15).re * (storedWidth 15 ^ 2)) (59 / 200) 0) -
      (momentScalarAmp2622K15P119Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K15P119Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K15P119 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentPanelPhase2622K15P119]
  have h := compactExp_real_error2620 momentPanelPhase2622K15P119 20 hsmall
  change |Real.exp (momentPanelPhase2622K15P119 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K15P119Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K15P119Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K15P119_replay] at h
  simpa only [momentPanelPhase_owner2622K15P119] using h

theorem momentScalarAmp2622K15P119_radius_le :
    (momentScalarAmp2622K15P119Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentScalarAmp2622K15P119Expected]

def momentScalarGrow2622K15P119Input : RatPair2542 := (momentPanelGrowth2622K15P119 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K15P119Expected : RatState2542 :=
  ((((2696034269704508096177586920464531034562469922956184347830665037590126757972386511798146140390239 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3417628701287659482198383733913600091226883440975 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K15P119_replay :
    compactExp2620 momentScalarGrow2622K15P119Input 20 = momentScalarGrow2622K15P119Expected := by
  decide +kernel

theorem momentScalarGrow2622K15P119_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 15).re * (storedWidth 15 ^ 2)) (59 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K15P119Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K15P119Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K15P119 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentPanelGrowth2622K15P119]
  have h := compactExp_real_error2620 momentPanelGrowth2622K15P119 20 hsmall
  change |Real.exp (momentPanelGrowth2622K15P119 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K15P119Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K15P119Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K15P119_replay] at h
  simpa only [momentPanelGrowth_owner2622K15P119] using h

theorem momentScalarGrow2622K15P119_radius_le :
    (momentScalarGrow2622K15P119Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, momentScalarGrow2622K15P119Expected]

end ConnesWeilRH.Dev
