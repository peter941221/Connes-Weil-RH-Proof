import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P149 : ℚ := ((-1770254093697623032908019629015995364782516060236037963 : ℚ) / 39337230007284583857776054575579205150926709352038400)

def momentPanelGrowth2622P149 : ℚ := ((2062311829758864222814322396333673083612820436471 : ℚ) / 2283596308329535809693257551119192218212394598400)

theorem momentPanelPhase_owner2622P149 :
    (momentPanelPhase2622P149 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (119 / 200) 0 := by
  norm_num [momentPanelPhase2622P149, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P149 :
    (momentPanelGrowth2622P149 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (119 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P149, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P149Input : RatPair2542 := (momentPanelPhase2622P149 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P149Expected : RatState2542 :=
  ((((30510377519955415460309401928385797831221153340755855429577964029889969887445 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((77358734453753531903134623745 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P149_replay :
    compactExp2620 momentScalarAmp2622P149Input 20 = momentScalarAmp2622P149Expected := by
  decide +kernel

theorem momentScalarAmp2622P149_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (119 / 200) 0) -
      (momentScalarAmp2622P149Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P149Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P149 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P149]
  have h := compactExp_real_error2620 momentPanelPhase2622P149 20 hsmall
  change |Real.exp (momentPanelPhase2622P149 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P149Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P149Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P149_replay] at h
  simpa only [momentPanelPhase_owner2622P149] using h

theorem momentScalarAmp2622P149_radius_le :
    (momentScalarAmp2622P149Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 91 := by
  norm_num [momentScalarAmp2622P149Expected]

def momentScalarGrow2622P149Input : RatPair2542 := (momentPanelGrowth2622P149 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P149Expected : RatState2542 :=
  ((((1317495703904114210721357632626939535724406628186714580598671264124011126700484432472339182721507 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((6680491125755661052981331967378037706443478039205 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P149_replay :
    compactExp2620 momentScalarGrow2622P149Input 20 = momentScalarGrow2622P149Expected := by
  decide +kernel

theorem momentScalarGrow2622P149_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (119 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P149Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P149Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P149 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P149]
  have h := compactExp_real_error2620 momentPanelGrowth2622P149 20 hsmall
  change |Real.exp (momentPanelGrowth2622P149 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P149Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P149Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P149_replay] at h
  simpa only [momentPanelGrowth_owner2622P149] using h

theorem momentScalarGrow2622P149_radius_le :
    (momentScalarGrow2622P149Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P149Expected]

end ConnesWeilRH.Dev
