import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K05
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K05P155 : ℚ := ((-797023713420109655450823959991726517033 : ℚ) / 15440998431260016693751042404043980800)

def momentPanelGrowth2622K05P155 : ℚ := ((2538440792880431337527837970585812052969 : ℚ) / 2019033760525589366605774273880313036800)

theorem momentPanelPhase_owner2622K05P155 :
    (momentPanelPhase2622K05P155 : ℝ) = momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (131 / 200) 0 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P155, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K05P155 :
    (momentPanelGrowth2622K05P155 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2))
      (131 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P155, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K05P155Input : RatPair2542 := (momentPanelPhase2622K05P155 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K05P155Expected : RatState2542 :=
  ((((40872396161799883135739018122358888180407253563332653785784344942704406511 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((106046787822744207040814781 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K05P155_replay :
    compactExp2620 momentScalarAmp2622K05P155Input 20 = momentScalarAmp2622K05P155Expected := by
  decide +kernel

theorem momentScalarAmp2622K05P155_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (131 / 200) 0) -
      (momentScalarAmp2622K05P155Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K05P155Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K05P155 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelPhase2622K05P155]
  have h := compactExp_real_error2620 momentPanelPhase2622K05P155 20 hsmall
  change |Real.exp (momentPanelPhase2622K05P155 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K05P155Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K05P155Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K05P155_replay] at h
  simpa only [momentPanelPhase_owner2622K05P155] using h

theorem momentScalarAmp2622K05P155_radius_le :
    (momentScalarAmp2622K05P155Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 94 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarAmp2622K05P155Expected]

def momentScalarGrow2622K05P155Input : RatPair2542 := (momentPanelGrowth2622K05P155 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K05P155Expected : RatState2542 :=
  ((((3754807128461882157182854805561774181920031146264948280286471452760568229225426900948755959089497 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((9519555606203249545262969320196412539980342017335 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K05P155_replay :
    compactExp2620 momentScalarGrow2622K05P155Input 20 = momentScalarGrow2622K05P155Expected := by
  decide +kernel

theorem momentScalarGrow2622K05P155_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 5).re * (storedWidth 5 ^ 2)) (131 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K05P155Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K05P155Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K05P155 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentPanelGrowth2622K05P155]
  have h := compactExp_real_error2620 momentPanelGrowth2622K05P155 20 hsmall
  change |Real.exp (momentPanelGrowth2622K05P155 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K05P155Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K05P155Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K05P155_replay] at h
  simpa only [momentPanelGrowth_owner2622K05P155] using h

theorem momentScalarGrow2622K05P155_radius_le :
    (momentScalarGrow2622K05P155Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, momentScalarGrow2622K05P155Expected]

end ConnesWeilRH.Dev
