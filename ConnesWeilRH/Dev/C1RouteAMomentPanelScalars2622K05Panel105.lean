import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P105 : ℚ := ((-805523175613791974885385524242019274133 : ℚ) / 26393499617231918722682558098492620800)

def momentPanelGrowth2622K05P105 : ℚ := ((14445765158063341505683554201547409803 : ℚ) / 125372672603532252975066341736815001600)

theorem momentPanelPhase_owner2622K05P105 :
    (momentPanelPhase2622K05P105 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (31 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P105, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P105 :
    (momentPanelGrowth2622K05P105 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (31 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P105, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P105Input : RatPair2542 := (momentPanelPhase2622K05P105 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P105Expected : RatState2542 :=
  ((((118860313763769758629191417949021133225069910192767489639877728495819473536273516129 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((75338866818380764749625175201967563 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K05P105_replay :
    compactExp2620 momentScalarAmp2622K05P105Input 20 = momentScalarAmp2622K05P105Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P105_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (31 / 200) 0) -
      (momentScalarAmp2622K05P105Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P105Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P105 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P105]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P105 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P105 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P105Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P105Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P105_replay] at h
  simpa only [momentPanelPhase_owner2622K05P105] using h

theorem momentScalarAmp2622K05P105_radius_le :
    (momentScalarAmp2622K05P105Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P105Expected]

def momentScalarGrow2622K05P105Input : RatPair2542 := (momentPanelGrowth2622K05P105 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P105Expected : RatState2542 :=
  ((((1198420296550816428927331365604511541205185848633818706988872981501388670961558310253090451426223 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3038356082627400735113483044216200999965579500429 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P105_replay :
    compactExp2620 momentScalarGrow2622K05P105Input 20 = momentScalarGrow2622K05P105Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P105_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (31 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P105Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P105Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P105 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P105]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P105 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P105 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P105Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P105Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P105_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P105] using h

theorem momentScalarGrow2622K05P105_radius_le :
    (momentScalarGrow2622K05P105Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P105Expected]

end ConnesWeilRH.Dev
