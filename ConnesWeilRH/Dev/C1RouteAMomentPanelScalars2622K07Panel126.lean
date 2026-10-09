import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P126 : ℚ := ((-29688830795292635532203283625768859425 : ℚ) / 937615231157609420358233532449947648)

def momentPanelGrowth2622K07P126 : ℚ := ((381503478692871994412743271958047976025 : ℚ) / 1007280724321582482986976528538621968384)

theorem momentPanelPhase_owner2622K07P126 :
    (momentPanelPhase2622K07P126 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (73 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P126, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P126 :
    (momentPanelGrowth2622K07P126 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (73 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P126, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P126Input : RatPair2542 := (momentPanelPhase2622K07P126 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P126Expected : RatState2542 :=
  ((((4730682443373449654496697799757627802589520558954395574271056723166588632484167189 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((47976268246342078004790643620949829 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P126_replay :
    compactExp2620 momentScalarAmp2622K07P126Input 20 = momentScalarAmp2622K07P126Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P126_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (73 / 200) 0) -
      (momentScalarAmp2622K07P126Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P126Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P126 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P126]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P126 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P126 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P126Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P126Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P126_replay] at h
  simpa only [momentPanelPhase_owner2622K07P126] using h

theorem momentScalarAmp2622K07P126_radius_le :
    (momentScalarAmp2622K07P126Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P126Expected]

def momentScalarGrow2622K07P126Input : RatPair2542 := (momentPanelGrowth2622K07P126 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P126Expected : RatState2542 :=
  ((((779876601198256464981161694373591941846462212784290889731012600303827144221392989840615746094459 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3954442738105643939708864329073636316461985147975 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P126_replay :
    compactExp2620 momentScalarGrow2622K07P126Input 20 = momentScalarGrow2622K07P126Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P126_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (73 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P126Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P126Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P126 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P126]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P126 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P126 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P126Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P126Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P126_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P126] using h

theorem momentScalarGrow2622K07P126_radius_le :
    (momentScalarGrow2622K07P126Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P126Expected]

end ConnesWeilRH.Dev
