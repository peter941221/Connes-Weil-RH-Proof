import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K22
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K22P128 : ℚ := ((-797561049521308943147424489926558828559 : ℚ) / 23034732586867202100476893285528371200)

def momentPanelGrowth2622K22P128 : ℚ := ((24859627802029470596425780301612684644729 : ℚ) / 72908610908898237608774834872168271052800)

theorem momentPanelPhase_owner2622K22P128 :
    (momentPanelPhase2622K22P128 : ℝ) = momentPhase2619 ((capturedNodes2584 22).re * (storedWidth 22 ^ 2)) (77 / 200) 0 := by
  norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentPanelPhase2622K22P128, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K22P128 :
    (momentPanelGrowth2622K22P128 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 22).re * (storedWidth 22 ^ 2))
      (77 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentPanelGrowth2622K22P128, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K22P128Input : RatPair2542 := (momentPanelPhase2622K22P128 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K22P128Expected : RatState2542 :=
  ((((1960940949814324601738593185900212852718257311043404865103809346387191192530749543 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2485870057250375693456618312315139 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K22P128_replay :
    compactExp2620 momentScalarAmp2622K22P128Input 20 = momentScalarAmp2622K22P128Expected := by
  decide +kernel

theorem momentScalarAmp2622K22P128_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 22).re * (storedWidth 22 ^ 2)) (77 / 200) 0) -
      (momentScalarAmp2622K22P128Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K22P128Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K22P128 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentPanelPhase2622K22P128]
  have h := compactExp_real_error2620 momentPanelPhase2622K22P128 20 hsmall
  change |Real.exp (momentPanelPhase2622K22P128 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K22P128Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K22P128Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K22P128_replay] at h
  simpa only [momentPanelPhase_owner2622K22P128] using h

theorem momentScalarAmp2622K22P128_radius_le :
    (momentScalarAmp2622K22P128Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentScalarAmp2622K22P128Expected]

def momentScalarGrow2622K22P128Input : RatPair2542 := (momentPanelGrowth2622K22P128 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K22P128Expected : RatState2542 :=
  ((((3003861297287544675361824105307161820258329993985344206350937358286511854296436764051287466557287 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((951961334574049634150807317094714757910989788989 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K22P128_replay :
    compactExp2620 momentScalarGrow2622K22P128Input 20 = momentScalarGrow2622K22P128Expected := by
  decide +kernel

theorem momentScalarGrow2622K22P128_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 22).re * (storedWidth 22 ^ 2)) (77 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K22P128Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K22P128Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K22P128 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentPanelGrowth2622K22P128]
  have h := compactExp_real_error2620 momentPanelGrowth2622K22P128 20 hsmall
  change |Real.exp (momentPanelGrowth2622K22P128 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K22P128Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K22P128Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K22P128_replay] at h
  simpa only [momentPanelGrowth_owner2622K22P128] using h

theorem momentScalarGrow2622K22P128_radius_le :
    (momentScalarGrow2622K22P128Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, momentScalarGrow2622K22P128Expected]

end ConnesWeilRH.Dev
