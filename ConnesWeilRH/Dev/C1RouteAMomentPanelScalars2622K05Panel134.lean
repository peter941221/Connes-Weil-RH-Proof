import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P134 : ℚ := ((-797676679343748230137675796884273843747 : ℚ) / 21687980589184731184326795800136908800)

def momentPanelGrowth2622K05P134 : ℚ := ((45266333708850239043458710259986917729 : ℚ) / 103197914183859881700564811905813708800)

theorem momentPanelPhase_owner2622K05P134 :
    (momentPanelPhase2622K05P134 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (89 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P134, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P134 :
    (momentPanelGrowth2622K05P134 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (89 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P134, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P134Input : RatPair2542 := (momentPanelPhase2622K05P134 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P134Expected : RatState2542 :=
  ((((227191815131719951285001028984660966429655820356210511137699046541035961991463609 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((288009945245038952964057785740957 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P134_replay :
    compactExp2620 momentScalarAmp2622K05P134Input 20 = momentScalarAmp2622K05P134Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P134_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (89 / 200) 0) -
      (momentScalarAmp2622K05P134Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P134Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P134 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P134]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P134 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P134 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P134Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P134Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P134_replay] at h
  simpa only [momentPanelPhase_owner2622K05P134] using h

theorem momentScalarAmp2622K05P134_radius_le :
    (momentScalarAmp2622K05P134Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P134Expected]

def momentScalarGrow2622K05P134Input : RatPair2542 := (momentPanelGrowth2622K05P134 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P134Expected : RatState2542 :=
  ((((1656021106352257981866315319388848005700155501643950948370435723327107843680826054281433957530591 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4198510542611561024206529773240794938606037267031 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P134_replay :
    compactExp2620 momentScalarGrow2622K05P134Input 20 = momentScalarGrow2622K05P134Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P134_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (89 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P134Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P134Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P134 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P134]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P134 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P134 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P134Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P134Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P134_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P134] using h

theorem momentScalarGrow2622K05P134_radius_le :
    (momentScalarGrow2622K05P134Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P134Expected]

end ConnesWeilRH.Dev
