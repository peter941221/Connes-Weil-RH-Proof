import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P063 : ℚ := ((-820699474126196847002685075411976257649 : ℚ) / 25144103185646975824567407419274035200)

def momentPanelGrowth2622K05P063 : ℚ := ((17658825904689485391642553303462397859249 : ℚ) / 87165116619304996749767357801108917452800)

theorem momentPanelPhase_owner2622K05P063 :
    (momentPanelPhase2622K05P063 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-53 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P063, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P063 :
    (momentPanelGrowth2622K05P063 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-53 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P063, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P063Input : RatPair2542 := (momentPanelPhase2622K05P063 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P063Expected : RatState2542 :=
  ((((7132910036470822849317221733849961571873083066919507148087467044874318809210442215 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4521159576609455914587753609990735 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622K05P063_replay :
    compactExp2620 momentScalarAmp2622K05P063Input 20 = momentScalarAmp2622K05P063Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P063_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-53 / 200) 0) -
      (momentScalarAmp2622K05P063Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P063Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P063 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P063]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P063 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P063 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P063Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P063Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P063_replay] at h
  simpa only [momentPanelPhase_owner2622K05P063] using h

theorem momentScalarAmp2622K05P063_radius_le :
    (momentScalarAmp2622K05P063Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P063Expected]

def momentScalarGrow2622K05P063Input : RatPair2542 := (momentPanelGrowth2622K05P063 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P063Expected : RatState2542 :=
  ((((2615667615425215693263436117842303193053810898761903930706529668995207610121622423690419012249457 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((828937995517540358859132161951390008284450144583 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K05P063_replay :
    compactExp2620 momentScalarGrow2622K05P063Input 20 = momentScalarGrow2622K05P063Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P063_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-53 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P063Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P063Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P063 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P063]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P063 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P063 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P063Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P063Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P063_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P063] using h

theorem momentScalarGrow2622K05P063_radius_le :
    (momentScalarGrow2622K05P063Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P063Expected]

end ConnesWeilRH.Dev
