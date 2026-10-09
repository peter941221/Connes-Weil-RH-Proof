import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P165 : ℚ := ((-798907362542743881556190171620996651213 : ℚ) / 11627905425773502654048959162272972800)

def momentPanelGrowth2622K05P165 : ℚ := ((946029420219419202482428277596215307 : ℚ) / 368125734306277818194642610841190400)

theorem momentPanelPhase_owner2622K05P165 :
    (momentPanelPhase2622K05P165 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (151 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P165, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P165 :
    (momentPanelGrowth2622K05P165 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (151 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P165, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P165Input : RatPair2542 := (momentPanelPhase2622K05P165 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P165Expected : RatState2542 :=
  ((((3097016716590404980482140430821436465881843487256338722684347003537 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417855565421612086146291 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P165_replay :
    compactExp2620 momentScalarAmp2622K05P165Input 20 = momentScalarAmp2622K05P165Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P165_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (151 / 200) 0) -
      (momentScalarAmp2622K05P165Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P165Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P165 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P165]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P165 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P165 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P165Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P165Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P165_replay] at h
  simpa only [momentPanelPhase_owner2622K05P165] using h

theorem momentScalarAmp2622K05P165_radius_le :
    (momentScalarAmp2622K05P165Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P165Expected]

def momentScalarGrow2622K05P165Input : RatPair2542 := (momentPanelGrowth2622K05P165 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P165Expected : RatState2542 :=
  ((((27904359515145749907370423707526454609978649694577717679421497799813914370317407881869592003626955 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2210805712264672968481789306506493946602915236149 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K05P165_replay :
    compactExp2620 momentScalarGrow2622K05P165Input 20 = momentScalarGrow2622K05P165Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P165_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (151 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P165Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P165Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P165 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P165]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P165 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P165 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P165Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P165Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P165_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P165] using h

theorem momentScalarGrow2622K05P165_radius_le :
    (momentScalarGrow2622K05P165Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P165Expected]

end ConnesWeilRH.Dev
