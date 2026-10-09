import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P131 : ℚ := ((-28484088965906325123717672580276299673626763087476617 : ℚ) / 787626639219783960362015112240703891012818724454400)

def momentPanelGrowth2622K01P131 : ℚ := ((56479554251961612164903982012840667006618222257374313 : ℚ) / 151269736888018887562721581501192877257176576006553600)

theorem momentPanelPhase_owner2622K01P131 :
    (momentPanelPhase2622K01P131 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (83 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P131, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P131 :
    (momentPanelGrowth2622K01P131 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (83 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P131, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P131Input : RatPair2542 := (momentPanelPhase2622K01P131 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P131Expected : RatState2542 :=
  ((((210157512750763625316109111570597452084600423064415411961451773865727615989933029 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((532830973330414596881427756695047 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P131_replay :
    compactExp2620 momentScalarAmp2622K01P131Input 20 = momentScalarAmp2622K01P131Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P131_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (83 / 200) 0) -
      (momentScalarAmp2622K01P131Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P131Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P131 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P131]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P131 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P131 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P131Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P131Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P131_replay] at h
  simpa only [momentPanelPhase_owner2622K01P131] using h

theorem momentScalarAmp2622K01P131_radius_le :
    (momentScalarAmp2622K01P131Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P131Expected]

def momentScalarGrow2622K01P131Input : RatPair2542 := (momentPanelGrowth2622K01P131 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P131Expected : RatState2542 :=
  ((((3102780579389154866546586091402049885943207916208986575944167866770548380484446306272501855982353 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3933240263317432956764900923931143771255300965767 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P131_replay :
    compactExp2620 momentScalarGrow2622K01P131Input 20 = momentScalarGrow2622K01P131Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P131_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (83 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P131Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P131Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P131 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P131]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P131 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P131 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P131Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P131Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P131_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P131] using h

theorem momentScalarGrow2622K01P131_radius_le :
    (momentScalarGrow2622K01P131Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P131Expected]

end ConnesWeilRH.Dev
