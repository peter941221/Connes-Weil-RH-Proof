import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P070 : ℚ := ((-351296262001803620613831429237063750058039215756699399 : ℚ) / 10983812793526526052648357163689424670574341468979200)

def momentPanelGrowth2622K02P070 : ℚ := ((73257546920571448992947733589180706266975173037 : ℚ) / 428174307811787964317485790834848540914823987200)

theorem momentPanelPhase_owner2622K02P070 :
    (momentPanelPhase2622K02P070 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-39 / 200) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P070, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P070 :
    (momentPanelGrowth2622K02P070 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (-39 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P070, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P070Input : RatPair2542 := (momentPanelPhase2622K02P070 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P070Expected : RatState2542 :=
  ((((13755917266628729116624879745378930158656471913256631113460931761418950653706668673 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((34876457328195791592239611820562629 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P070_replay :
    compactExp2620 momentScalarAmp2622K02P070Input 20 = momentScalarAmp2622K02P070Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P070_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-39 / 200) 0) -
      (momentScalarAmp2622K02P070Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P070Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P070 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P070]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P070 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P070 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P070Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P070Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P070_replay] at h
  simpa only [momentPanelPhase_owner2622K02P070] using h

theorem momentScalarAmp2622K02P070_radius_le :
    (momentScalarAmp2622K02P070Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P070Expected]

def momentScalarGrow2622K02P070Input : RatPair2542 := (momentPanelGrowth2622K02P070 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P070Expected : RatState2542 :=
  ((((633641022143911351006506896645123224590337406215891055965928060674323407555872922506976331747877 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((1606470581977195515912121679584179769734829706951 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K02P070_replay :
    compactExp2620 momentScalarGrow2622K02P070Input 20 = momentScalarGrow2622K02P070Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P070_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (-39 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P070Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P070Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P070 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P070]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P070 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P070 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P070Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P070Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P070_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P070] using h

theorem momentScalarGrow2622K02P070_radius_le :
    (momentScalarGrow2622K02P070Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P070Expected]

end ConnesWeilRH.Dev
