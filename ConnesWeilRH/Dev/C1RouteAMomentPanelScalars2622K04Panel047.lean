import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P047 : ℚ := ((-1013848643230001224118004387623299480640528965637083 : ℚ) / 24948289668500178720898838745977174983970410987520)

def momentPanelGrowth2622K04P047 : ℚ := ((1526761232817886018457593526233817647102717635746608709 : ℚ) / 3160820847780014001720504364178236230553372092845260800)

theorem momentPanelPhase_owner2622K04P047 :
    (momentPanelPhase2622K04P047 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-17 / 40) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P047, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P047 :
    (momentPanelGrowth2622K04P047 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-17 / 40) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P047, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P047Input : RatPair2542 := (momentPanelPhase2622K04P047 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P047Expected : RatState2542 :=
  ((((2397224078250435657607122008494054019653250701151430155445926369885015947090653 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((6077923048997539481132246565135 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P047_replay :
    compactExp2620 momentScalarAmp2622K04P047Input 20 = momentScalarAmp2622K04P047Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P047_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-17 / 40) 0) -
      (momentScalarAmp2622K04P047Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P047Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P047 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P047]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P047 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P047 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P047Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P047Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P047_replay] at h
  simpa only [momentPanelPhase_owner2622K04P047] using h

theorem momentScalarAmp2622K04P047_radius_le :
    (momentScalarAmp2622K04P047Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P047Expected]

def momentScalarGrow2622K04P047Input : RatPair2542 := (momentPanelGrowth2622K04P047 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P047Expected : RatState2542 :=
  ((((3462378112161186720252541276324541872398997124548364208242982748150667790964948965665244363776373 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((274317729391573215475909040415043191489039940989 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarGrow2622K04P047_replay :
    compactExp2620 momentScalarGrow2622K04P047Input 20 = momentScalarGrow2622K04P047Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P047_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-17 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P047Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P047Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P047 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P047]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P047 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P047 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P047Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P047Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P047_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P047] using h

theorem momentScalarGrow2622K04P047_radius_le :
    (momentScalarGrow2622K04P047Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P047Expected]

end ConnesWeilRH.Dev
