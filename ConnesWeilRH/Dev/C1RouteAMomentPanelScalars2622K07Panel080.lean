import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P080 : ℚ := ((-33274044644904849518800179637201210525 : ℚ) / 1071965912372198085246460124968517632)

def momentPanelGrowth2622K07P080 : ℚ := ((18812523584043259229671691714753425 : ℚ) / 132525264350260014550071339902828544)

theorem momentPanelPhase_owner2622K07P080 :
    (momentPanelPhase2622K07P080 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-19 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P080, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P080 :
    (momentPanelGrowth2622K07P080 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-19 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P080, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P080Input : RatPair2542 := (momentPanelPhase2622K07P080 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P080Expected : RatState2542 :=
  ((((70633001195925921006355119048626813107167647705397985298745160268796637605851034905 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((22385154232188630460743158261793747 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K07P080_replay :
    compactExp2620 momentScalarAmp2622K07P080Input 20 = momentScalarAmp2622K07P080Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P080_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-19 / 200) 0) -
      (momentScalarAmp2622K07P080Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P080Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P080 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P080]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P080 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P080 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P080Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P080Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P080_replay] at h
  simpa only [momentPanelPhase_owner2622K07P080] using h

theorem momentScalarAmp2622K07P080_radius_le :
    (momentScalarAmp2622K07P080Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P080Expected]

def momentScalarGrow2622K07P080Input : RatPair2542 := (momentPanelGrowth2622K07P080 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P080Expected : RatState2542 :=
  ((((615444033300551852699058876374487731061056010503734915277294437583102079538215661738740427447919 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3120671570410642415339145805435259871780861259805 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P080_replay :
    compactExp2620 momentScalarGrow2622K07P080Input 20 = momentScalarGrow2622K07P080Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P080_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-19 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P080Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P080Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P080 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P080]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P080 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P080 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P080Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P080Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P080_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P080] using h

theorem momentScalarGrow2622K07P080_radius_le :
    (momentScalarGrow2622K07P080Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P080Expected]

end ConnesWeilRH.Dev
