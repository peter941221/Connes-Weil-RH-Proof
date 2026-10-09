import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P159 : ℚ := ((-29313949924311778823208921385934478475 : ℚ) / 559226597591883856929073612458033152)

def momentPanelGrowth2622K07P159 : ℚ := ((59630207648357247266360675186611825 : ℚ) / 35169698252731996515124533729951744)

theorem momentPanelPhase_owner2622K07P159 :
    (momentPanelPhase2622K07P159 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (139 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P159, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P159 :
    (momentPanelGrowth2622K07P159 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (139 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P159, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P159Input : RatPair2542 := (momentPanelPhase2622K07P159 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P159Expected : RatState2542 :=
  ((((36680221740315233862858131690640837622074495775377794267908249361331965595 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((24458940620915078501161981 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P159_replay :
    compactExp2620 momentScalarAmp2622K07P159Input 20 = momentScalarAmp2622K07P159Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P159_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (139 / 200) 0) -
      (momentScalarAmp2622K07P159Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P159Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P159 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P159]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P159 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P159 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P159Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P159Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P159_replay] at h
  simpa only [momentPanelPhase_owner2622K07P159] using h

theorem momentScalarAmp2622K07P159_radius_le :
    (momentScalarAmp2622K07P159Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 94 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P159Expected]

def momentScalarGrow2622K07P159Input : RatPair2542 := (momentPanelGrowth2622K07P159 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P159Expected : RatState2542 :=
  ((((5819889199491024736912676620730947419644809511027725373271145114468333607842756879956987241830719 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((14755148215572399648181662882685105306167688920201 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P159_replay :
    compactExp2620 momentScalarGrow2622K07P159Input 20 = momentScalarGrow2622K07P159Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P159_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (139 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P159Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P159Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P159 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P159]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P159 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P159 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P159Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P159Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P159_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P159] using h

theorem momentScalarGrow2622K07P159_radius_le :
    (momentScalarGrow2622K07P159Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P159Expected]

end ConnesWeilRH.Dev
