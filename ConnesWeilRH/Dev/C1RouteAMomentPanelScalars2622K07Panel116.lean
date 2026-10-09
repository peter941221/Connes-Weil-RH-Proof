import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P116 : ℚ := ((-30300018992158495080300778787632575925 : ℚ) / 1005764127425879032982696296770961408)

def momentPanelGrowth2622K07P116 : ℚ := ((938644585373362411643663515092674904075 : ℚ) / 3486604664772199869990694312044356698112)

theorem momentPanelPhase_owner2622K07P116 :
    (momentPanelPhase2622K07P116 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (53 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P116, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P116 :
    (momentPanelGrowth2622K07P116 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (53 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P116, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P116Input : RatPair2542 := (momentPanelPhase2622K07P116 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P116Expected : RatState2542 :=
  ((((44037613030756209680341982318230691986346198454006025270829840647308796075388599991 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((223303641953859736842125427736076801 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P116_replay :
    compactExp2620 momentScalarAmp2622K07P116Input 20 = momentScalarAmp2622K07P116Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P116_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (53 / 200) 0) -
      (momentScalarAmp2622K07P116Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P116Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P116 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P116]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P116 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P116 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P116Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P116Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P116_replay] at h
  simpa only [momentPanelPhase_owner2622K07P116] using h

theorem momentScalarAmp2622K07P116_radius_le :
    (momentScalarAmp2622K07P116Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P116Expected]

def momentScalarGrow2622K07P116Input : RatPair2542 := (momentPanelGrowth2622K07P116 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P116Expected : RatState2542 :=
  ((((1397935054380894524171475931448771550807358053091306181624507593777033970834871014606826760636739 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3544185511587219288972568643377891241869738114099 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P116_replay :
    compactExp2620 momentScalarGrow2622K07P116Input 20 = momentScalarGrow2622K07P116Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P116_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (53 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P116Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P116Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P116 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P116]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P116 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P116 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P116Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P116Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P116_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P116] using h

theorem momentScalarGrow2622K07P116_radius_le :
    (momentScalarGrow2622K07P116Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P116Expected]

end ConnesWeilRH.Dev
