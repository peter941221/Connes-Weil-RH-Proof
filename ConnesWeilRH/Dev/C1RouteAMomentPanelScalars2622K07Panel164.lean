import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P164 : ℚ := ((-29556663230869108429411393609949696725 : ℚ) / 481342144713861442501116167519731712)

def momentPanelGrowth2622K07P164 : ℚ := ((24167720968069330636842309650478807 : ℚ) / 9938380705789318507734153130147840)

theorem momentPanelPhase_owner2622K07P164 :
    (momentPanelPhase2622K07P164 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (149 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P164, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P164 :
    (momentPanelGrowth2622K07P164 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (149 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P164, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P164Input : RatPair2542 := (momentPanelPhase2622K07P164 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P164Expected : RatState2542 :=
  ((((4590736240301255708736324791159571957621896591503267857051444648898355 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1211835714788676224859583 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P164_replay :
    compactExp2620 momentScalarAmp2622K07P164Input 20 = momentScalarAmp2622K07P164Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P164_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (149 / 200) 0) -
      (momentScalarAmp2622K07P164Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P164Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P164 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P164]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P164 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P164 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P164Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P164Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P164_replay] at h
  simpa only [momentPanelPhase_owner2622K07P164] using h

theorem momentScalarAmp2622K07P164_radius_le :
    (momentScalarAmp2622K07P164Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P164Expected]

def momentScalarGrow2622K07P164Input : RatPair2542 := (momentPanelGrowth2622K07P164 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P164Expected : RatState2542 :=
  ((((3038134629109274792331504655028520576830675831899653197148498194326481459735611766692048752128087 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((240705265914180554936040335230240964456254579417 : ℚ) / 20173827172553973356686868531273530268200826506478308693989526222973809547006571833044104322501076808092993531037089792))

theorem momentScalarGrow2622K07P164_replay :
    compactExp2620 momentScalarGrow2622K07P164Input 20 = momentScalarGrow2622K07P164Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P164_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (149 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P164Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P164Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P164 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P164]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P164 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P164 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P164Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P164Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P164_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P164] using h

theorem momentScalarGrow2622K07P164_radius_le :
    (momentScalarGrow2622K07P164Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P164Expected]

end ConnesWeilRH.Dev
