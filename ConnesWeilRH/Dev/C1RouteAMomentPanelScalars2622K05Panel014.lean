import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P014 : ℚ := ((-823685405749389752359589931260283348787 : ℚ) / 11627905425773502654048959162272972800)

def momentPanelGrowth2622K05P014 : ℚ := ((946029420219419202482428277596215307 : ℚ) / 368125734306277818194642610841190400)

theorem momentPanelPhase_owner2622K05P014 :
    (momentPanelPhase2622K05P014 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-151 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P014, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P014 :
    (momentPanelGrowth2622K05P014 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-151 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P014, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P014Input : RatPair2542 := (momentPanelPhase2622K05P014 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P014Expected : RatState2542 :=
  ((((367705585156660878719013808326086863290489446498585369037321275405 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1208926052691478107574287 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P014_replay :
    compactExp2620 momentScalarAmp2622K05P014Input 20 = momentScalarAmp2622K05P014Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P014_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-151 / 200) 0) -
      (momentScalarAmp2622K05P014Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P014Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P014 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P014]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P014 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P014 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P014Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P014Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P014_replay] at h
  simpa only [momentPanelPhase_owner2622K05P014] using h

theorem momentScalarAmp2622K05P014_radius_le :
    (momentScalarAmp2622K05P014Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P014Expected]

def momentScalarGrow2622K05P014Input : RatPair2542 := (momentPanelGrowth2622K05P014 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P014Expected : RatState2542 :=
  ((((27904359515145749907370423707526454609978649694577717679421497799813914370317407881869592003626955 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2210805712264672968481789306506493946602915236149 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K05P014_replay :
    compactExp2620 momentScalarGrow2622K05P014Input 20 = momentScalarGrow2622K05P014Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P014_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-151 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P014Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P014Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P014 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P014]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P014 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P014 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P014Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P014Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P014_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P014] using h

theorem momentScalarGrow2622K05P014_radius_le :
    (momentScalarGrow2622K05P014Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P014Expected]

end ConnesWeilRH.Dev
