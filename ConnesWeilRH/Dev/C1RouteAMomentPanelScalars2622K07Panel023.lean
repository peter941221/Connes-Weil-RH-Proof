import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P023 : ℚ := ((-35691267435675251512704962854956010075 : ℚ) / 603361120889429891771582831256403968)

def momentPanelGrowth2622K07P023 : ℚ := ((576724135340185420925667207108170820025 : ℚ) / 410666344162711282865215510949998362624)

theorem momentPanelPhase_owner2622K07P023 :
    (momentPanelPhase2622K07P023 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-133 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P023, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P023 :
    (momentPanelGrowth2622K07P023 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-133 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P023, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P023Input : RatPair2542 := (momentPanelPhase2622K07P023 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P023Expected : RatState2542 :=
  ((((43582424034201071268847297857654396954431729963709616484478870159280973 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2473102042009118049960185 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P023_replay :
    compactExp2620 momentScalarAmp2622K07P023Input 20 = momentScalarAmp2622K07P023Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P023_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-133 / 200) 0) -
      (momentScalarAmp2622K07P023Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P023Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P023 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P023]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P023 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P023 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P023Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P023Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P023_replay] at h
  simpa only [momentPanelPhase_owner2622K07P023] using h

theorem momentScalarAmp2622K07P023_radius_le :
    (momentScalarAmp2622K07P023Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P023Expected]

def momentScalarGrow2622K07P023Input : RatPair2542 := (momentPanelGrowth2622K07P023 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P023Expected : RatState2542 :=
  ((((4349859271671612291357822090236713476498093772880727533742899579908512451271566838835603299112381 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((5514094331590407493225441428506590697783298255057 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K07P023_replay :
    compactExp2620 momentScalarGrow2622K07P023Input 20 = momentScalarGrow2622K07P023Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P023_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-133 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P023Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P023Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P023 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P023]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P023 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P023 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P023Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P023Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P023_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P023] using h

theorem momentScalarGrow2622K07P023_radius_le :
    (momentScalarGrow2622K07P023Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P023Expected]

end ConnesWeilRH.Dev
