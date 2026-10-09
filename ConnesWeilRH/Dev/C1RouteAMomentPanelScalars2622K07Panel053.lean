import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P053 : ℚ := ((-35214879936392709824427920489482340575 : ℚ) / 937615231157609420358233532449947648)

def momentPanelGrowth2622K07P053 : ℚ := ((381503478692871994412743271958047976025 : ℚ) / 1007280724321582482986976528538621968384)

theorem momentPanelPhase_owner2622K07P053 :
    (momentPanelPhase2622K07P053 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-73 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P053, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P053 :
    (momentPanelGrowth2622K07P053 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-73 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P053, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P053Input : RatPair2542 := (momentPanelPhase2622K07P053 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P053Expected : RatState2542 :=
  ((((52163922285445162733296620290366627707658894795768746666038411391849173332297043 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((66127997136175761203739473603701 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P053_replay :
    compactExp2620 momentScalarAmp2622K07P053Input 20 = momentScalarAmp2622K07P053Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P053_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-73 / 200) 0) -
      (momentScalarAmp2622K07P053Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P053Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P053 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P053]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P053 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P053 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P053Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P053Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P053_replay] at h
  simpa only [momentPanelPhase_owner2622K07P053] using h

theorem momentScalarAmp2622K07P053_radius_le :
    (momentScalarAmp2622K07P053Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P053Expected]

def momentScalarGrow2622K07P053Input : RatPair2542 := (momentPanelGrowth2622K07P053 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P053Expected : RatState2542 :=
  ((((779876601198256464981161694373591941846462212784290889731012600303827144221392989840615746094459 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3954442738105643939708864329073636316461985147975 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P053_replay :
    compactExp2620 momentScalarGrow2622K07P053Input 20 = momentScalarGrow2622K07P053Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P053_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-73 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P053Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P053Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P053 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P053]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P053 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P053 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P053Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P053Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P053_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P053] using h

theorem momentScalarGrow2622K07P053_radius_le :
    (momentScalarGrow2622K07P053Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P053Expected]

end ConnesWeilRH.Dev
