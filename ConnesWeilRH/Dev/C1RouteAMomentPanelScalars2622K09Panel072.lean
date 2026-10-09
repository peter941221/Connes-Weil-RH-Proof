import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K09
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K09P072 : ℚ := ((-6547213613219923112672179264317390411 : ℚ) / 209720115301758272183614578297405440)

def momentPanelGrowth2622K09P072 : ℚ := ((776440025561664267267381220182948991009 : ℚ) / 5934187851137678611881160084122553548800)

theorem momentPanelPhase_owner2622K09P072 :
    (momentPanelPhase2622K09P072 : ℝ) = momentPhase2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (-7 / 40) 0 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelPhase2622K09P072, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K09P072 :
    (momentPanelGrowth2622K09P072 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2))
      (-7 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelGrowth2622K09P072, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K09P072Input : RatPair2542 := (momentPanelPhase2622K09P072 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K09P072Expected : RatState2542 :=
  ((((14769958058797220889150721455314526972897313472483003163041122354915549939314166867 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((74894814575602044898243884632515465 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K09P072_replay :
    compactExp2620 momentScalarAmp2622K09P072Input 20 = momentScalarAmp2622K09P072Expected := by
  decide +kernel

theorem momentScalarAmp2622K09P072_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (-7 / 40) 0) -
      (momentScalarAmp2622K09P072Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K09P072Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K09P072 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelPhase2622K09P072]
  have h := compactExp_real_error2620 momentPanelPhase2622K09P072 20 hsmall
  change |Real.exp (momentPanelPhase2622K09P072 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K09P072Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K09P072Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K09P072_replay] at h
  simpa only [momentPanelPhase_owner2622K09P072] using h

theorem momentScalarAmp2622K09P072_radius_le :
    (momentScalarAmp2622K09P072Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentScalarAmp2622K09P072Expected]

def momentScalarGrow2622K09P072Input : RatPair2542 := (momentPanelGrowth2622K09P072 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K09P072Expected : RatState2542 :=
  ((((2434571306957533418970792336734736155776863540361511453020009721240453239889373633113770304628499 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3086185393467370314997015398768511395035785216541 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K09P072_replay :
    compactExp2620 momentScalarGrow2622K09P072Input 20 = momentScalarGrow2622K09P072Expected := by
  decide +kernel

theorem momentScalarGrow2622K09P072_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 9).re * (storedWidth 9 ^ 2)) (-7 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K09P072Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K09P072Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K09P072 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentPanelGrowth2622K09P072]
  have h := compactExp_real_error2620 momentPanelGrowth2622K09P072 20 hsmall
  change |Real.exp (momentPanelGrowth2622K09P072 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K09P072Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K09P072Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K09P072_replay] at h
  simpa only [momentPanelGrowth_owner2622K09P072] using h

theorem momentScalarGrow2622K09P072_radius_le :
    (momentScalarGrow2622K09P072Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, momentScalarGrow2622K09P072Expected]

end ConnesWeilRH.Dev
