import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P045 : ℚ := ((-824916088948385403778104305997006156253 : ℚ) / 21687980589184731184326795800136908800)

def momentPanelGrowth2622K05P045 : ℚ := ((45266333708850239043458710259986917729 : ℚ) / 103197914183859881700564811905813708800)

theorem momentPanelPhase_owner2622K05P045 :
    (momentPanelPhase2622K05P045 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-89 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P045, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P045 :
    (momentPanelGrowth2622K05P045 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (-89 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P045, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P045Input : RatPair2542 := (momentPanelPhase2622K05P045 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P045Expected : RatState2542 :=
  ((((64704235383981959476158357118607480555619536790777546300333999412445055285395801 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((82025340540591598499301860293317 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P045_replay :
    compactExp2620 momentScalarAmp2622K05P045Input 20 = momentScalarAmp2622K05P045Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P045_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-89 / 200) 0) -
      (momentScalarAmp2622K05P045Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P045Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P045 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P045]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P045 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P045 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P045Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P045Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P045_replay] at h
  simpa only [momentPanelPhase_owner2622K05P045] using h

theorem momentScalarAmp2622K05P045_radius_le :
    (momentScalarAmp2622K05P045Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P045Expected]

def momentScalarGrow2622K05P045Input : RatPair2542 := (momentPanelGrowth2622K05P045 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P045Expected : RatState2542 :=
  ((((1656021106352257981866315319388848005700155501643950948370435723327107843680826054281433957530591 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4198510542611561024206529773240794938606037267031 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P045_replay :
    compactExp2620 momentScalarGrow2622K05P045Input 20 = momentScalarGrow2622K05P045Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P045_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (-89 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P045Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P045Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P045 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P045]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P045 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P045 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P045Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P045Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P045_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P045] using h

theorem momentScalarGrow2622K05P045_radius_le :
    (momentScalarGrow2622K05P045Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P045Expected]

end ConnesWeilRH.Dev
