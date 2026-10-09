import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P000 : ℚ := ((-34007129876854554808941339839921038525 : ℚ) / 215236930713951526538928230647201792)

def momentPanelGrowth2622K07P000 : ℚ := ((220232313608349064567823303672665875 : ℚ) / 14643899733836506046089915428503552)

theorem momentPanelPhase_owner2622K07P000 :
    (momentPanelPhase2622K07P000 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-179 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P000, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P000 :
    (momentPanelGrowth2622K07P000 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-179 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P000, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P000Input : RatPair2542 := (momentPanelPhase2622K07P000 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P000Expected : RatState2542 :=
  ((((5148565482972066765260154827 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P000_replay :
    compactExp2620 momentScalarAmp2622K07P000Input 20 = momentScalarAmp2622K07P000Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P000_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-179 / 200) 0) -
      (momentScalarAmp2622K07P000Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P000Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P000 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P000]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P000 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P000 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P000Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P000Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P000_replay] at h
  simpa only [momentPanelPhase_owner2622K07P000] using h

theorem momentScalarAmp2622K07P000_radius_le :
    (momentScalarAmp2622K07P000Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P000Expected]

def momentScalarGrow2622K07P000Input : RatPair2542 := (momentPanelGrowth2622K07P000 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P000Expected : RatState2542 :=
  ((((7261620746581773185919451766282105840695868903795770992404448852561468242258493710482098637866863521533 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2301266468393789961464525518002269674051094378808054533 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K07P000_replay :
    compactExp2620 momentScalarGrow2622K07P000Input 20 = momentScalarGrow2622K07P000Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P000_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-179 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P000Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P000Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P000 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P000]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P000 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P000 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P000Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P000Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P000_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P000] using h

theorem momentScalarGrow2622K07P000_radius_le :
    (momentScalarGrow2622K07P000Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 65 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P000Expected]

end ConnesWeilRH.Dev
