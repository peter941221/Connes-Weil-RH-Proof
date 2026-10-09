import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K06
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K06P128 : ℚ := ((-19125511 : ℚ) / 567850)

def momentPanelGrowth2622K06P128 : ℚ := ((656893441 : ℚ) / 1797336025)

theorem momentPanelPhase_owner2622K06P128 :
    (momentPanelPhase2622K06P128 : ℝ) = momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (77 / 200) 0 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P128, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K06P128 :
    (momentPanelGrowth2622K06P128 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2))
      (77 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P128, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K06P128Input : RatPair2542 := (momentPanelPhase2622K06P128 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K06P128Expected : RatState2542 :=
  ((((5038641159284136525439605873878468905874210225130013059030762506395654910690816793 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((6387441655524297218144733873239669 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K06P128_replay :
    compactExp2620 momentScalarAmp2622K06P128Input 20 = momentScalarAmp2622K06P128Expected := by
  decide +kernel

theorem momentScalarAmp2622K06P128_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (77 / 200) 0) -
      (momentScalarAmp2622K06P128Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K06P128Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K06P128 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelPhase2622K06P128]
  have h := compactExp_real_error2620 momentPanelPhase2622K06P128 20 hsmall
  change |Real.exp (momentPanelPhase2622K06P128 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K06P128Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K06P128Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K06P128_replay] at h
  simpa only [momentPanelPhase_owner2622K06P128] using h

theorem momentScalarAmp2622K06P128_radius_le :
    (momentScalarAmp2622K06P128Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarAmp2622K06P128Expected]

def momentScalarGrow2622K06P128Input : RatPair2542 := (momentPanelGrowth2622K06P128 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K06P128Expected : RatState2542 :=
  ((((3078401781386639456471921112578620288487587905564720583740722997614053657475483386469816019195711 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3902336505756775015905768168825885603418479609641 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K06P128_replay :
    compactExp2620 momentScalarGrow2622K06P128Input 20 = momentScalarGrow2622K06P128Expected := by
  decide +kernel

theorem momentScalarGrow2622K06P128_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 6).re * (storedWidth 6 ^ 2)) (77 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K06P128Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K06P128Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K06P128 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentPanelGrowth2622K06P128]
  have h := compactExp_real_error2620 momentPanelGrowth2622K06P128 20 hsmall
  change |Real.exp (momentPanelGrowth2622K06P128 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K06P128Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K06P128Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K06P128_replay] at h
  simpa only [momentPanelGrowth_owner2622K06P128] using h

theorem momentScalarGrow2622K06P128_radius_le :
    (momentScalarGrow2622K06P128Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, momentScalarGrow2622K06P128Expected]

end ConnesWeilRH.Dev
