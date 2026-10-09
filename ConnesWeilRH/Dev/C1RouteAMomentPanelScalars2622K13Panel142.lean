import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K13
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K13P142 : ℚ := ((-19088827896954969018477760400612643909 : ℚ) / 470146254612645720427097284809850880)

def momentPanelGrowth2622K13P142 : ℚ := ((11020410726052090495093072437846792244163 : ℚ) / 17480219274064120567929771377129265561600)

theorem momentPanelPhase_owner2622K13P142 :
    (momentPanelPhase2622K13P142 : ℝ) = momentPhase2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2)) (21 / 40) 0 := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelPhase2622K13P142, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K13P142 :
    (momentPanelGrowth2622K13P142 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2))
      (21 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelGrowth2622K13P142, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K13P142Input : RatPair2542 := (momentPanelPhase2622K13P142 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K13P142Expected : RatState2542 :=
  ((((4970734338679356117019434876814813760958805397028175489809364615850612421659021 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((24614846786974067239584141401 : ℚ) / 10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896))

theorem momentScalarAmp2622K13P142_replay :
    compactExp2620 momentScalarAmp2622K13P142Input 20 = momentScalarAmp2622K13P142Expected := by
  decide +kernel

theorem momentScalarAmp2622K13P142_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2)) (21 / 40) 0) -
      (momentScalarAmp2622K13P142Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K13P142Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K13P142 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelPhase2622K13P142]
  have h := compactExp_real_error2620 momentPanelPhase2622K13P142 20 hsmall
  change |Real.exp (momentPanelPhase2622K13P142 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K13P142Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K13P142Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K13P142_replay] at h
  simpa only [momentPanelPhase_owner2622K13P142] using h

theorem momentScalarAmp2622K13P142_radius_le :
    (momentScalarAmp2622K13P142Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentScalarAmp2622K13P142Expected]

def momentScalarGrow2622K13P142Input : RatPair2542 := (momentPanelGrowth2622K13P142 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K13P142Expected : RatState2542 :=
  ((((1003089624691010680317245627522123543436933042371972555600188458463178053206917307742885871185983 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((5086265601199820822809365573681962042613178480149 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K13P142_replay :
    compactExp2620 momentScalarGrow2622K13P142Input 20 = momentScalarGrow2622K13P142Expected := by
  decide +kernel

theorem momentScalarGrow2622K13P142_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 13).re * (storedWidth 13 ^ 2)) (21 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K13P142Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K13P142Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K13P142 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentPanelGrowth2622K13P142]
  have h := compactExp_real_error2620 momentPanelGrowth2622K13P142 20 hsmall
  change |Real.exp (momentPanelGrowth2622K13P142 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K13P142Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K13P142Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K13P142_replay] at h
  simpa only [momentPanelGrowth_owner2622K13P142] using h

theorem momentScalarGrow2622K13P142_radius_le :
    (momentScalarGrow2622K13P142Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, momentScalarGrow2622K13P142Expected]

end ConnesWeilRH.Dev
