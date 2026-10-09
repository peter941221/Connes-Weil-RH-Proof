import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P069 : ℚ := ((-73216692136846050425500157533303199762421667388753525 : ℚ) / 2333470051703452871776958296035635376258153296429056)

def momentPanelGrowth2622K03P069 : ℚ := ((1175640841691633725670453288546372880885179719792882425 : ℚ) / 8346497099485092463265447117313886323135852167840137216)

theorem momentPanelPhase_owner2622K03P069 :
    (momentPanelPhase2622K03P069 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-41 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P069, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P069 :
    (momentPanelGrowth2622K03P069 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-41 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P069, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P069Input : RatPair2542 := (momentPanelPhase2622K03P069 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P069Expected : RatState2542 :=
  ((((50448921969699453625964979441809393276732273558600483371667940984665171302282621937 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((63953519883173809530647130153082377 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P069_replay :
    compactExp2620 momentScalarAmp2622K03P069Input 20 = momentScalarAmp2622K03P069Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P069_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-41 / 200) 0) -
      (momentScalarAmp2622K03P069Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P069Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P069 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P069]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P069 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P069 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P069Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P069Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P069_replay] at h
  simpa only [momentPanelPhase_owner2622K03P069] using h

theorem momentScalarAmp2622K03P069_radius_le :
    (momentScalarAmp2622K03P069Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P069Expected]

def momentScalarGrow2622K03P069Input : RatPair2542 := (momentPanelGrowth2622K03P069 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P069Expected : RatState2542 :=
  ((((614767513614453326570321007483924541594134186797034625383612560867751687867553888297151203385431 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3117241211800091647305004754127594313014074275605 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P069_replay :
    compactExp2620 momentScalarGrow2622K03P069Input 20 = momentScalarGrow2622K03P069Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P069_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-41 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P069Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P069Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P069 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P069]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P069 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P069 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P069Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P069Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P069_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P069] using h

theorem momentScalarGrow2622K03P069_radius_le :
    (momentScalarGrow2622K03P069Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P069Expected]

end ConnesWeilRH.Dev
