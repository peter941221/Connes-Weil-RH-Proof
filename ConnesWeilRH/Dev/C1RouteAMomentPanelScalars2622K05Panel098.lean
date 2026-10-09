import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P098 : ℚ := ((-808075933770612803386514476021075883419 : ℚ) / 26847825592353716140178976527299379200)

def momentPanelGrowth2622K05P098 : ℚ := ((6884287056339915209902661112701416504929 : ℚ) / 99775826484833044745879104971697081548800)

theorem momentPanelPhase_owner2622K05P098 :
    (momentPanelPhase2622K05P098 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (17 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P098, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P098 :
    (momentPanelGrowth2622K05P098 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (17 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P098, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P098Input : RatPair2542 := (momentPanelPhase2622K05P098 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P098Expected : RatState2542 :=
  ((((181150799551882227272587191842445940206380424185366690958677555877036417813144256855 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((114821255680579511816709987720436731 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P098_replay :
    compactExp2620 momentScalarAmp2622K05P098Input 20 = momentScalarAmp2622K05P098Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P098_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (17 / 200) 0) -
      (momentScalarAmp2622K05P098Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P098Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P098 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P098]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P098 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P098 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P098Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P098Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P098_replay] at h
  simpa only [momentPanelPhase_owner2622K05P098] using h

theorem momentScalarAmp2622K05P098_radius_le :
    (momentScalarAmp2622K05P098Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P098Expected]

def momentScalarGrow2622K05P098Input : RatPair2542 := (momentPanelGrowth2622K05P098 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P098Expected : RatState2542 :=
  ((((2288568233622981158428810282202586328185369273317528365533660611981041667516018438199447029794353 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1450552352059646647930168965355235992499874191303 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K05P098_replay :
    compactExp2620 momentScalarGrow2622K05P098Input 20 = momentScalarGrow2622K05P098Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P098_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (17 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P098Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P098Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P098 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P098]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P098 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P098 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P098Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P098Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P098_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P098] using h

theorem momentScalarGrow2622K05P098_radius_le :
    (momentScalarGrow2622K05P098Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P098Expected]

end ConnesWeilRH.Dev
