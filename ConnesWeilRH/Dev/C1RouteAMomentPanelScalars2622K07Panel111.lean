import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P111 : ℚ := ((-30660961287606927085422549990017101675 : ℚ) / 1031725611718553171125348778417061888)

def momentPanelGrowth2622K07P111 : ℚ := ((17333844514848932787852615070070073025 : ℚ) / 76527437981080495766572830143759253504)

theorem momentPanelPhase_owner2622K07P111 :
    (momentPanelPhase2622K07P111 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (43 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P111, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P111 :
    (momentPanelGrowth2622K07P111 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (43 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P111, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P111Input : RatPair2542 := (momentPanelPhase2622K07P111 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P111Expected : RatState2542 :=
  ((((66239411019401538843682862071638761309722674491189391583981906411490418702008221933 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((335883235826199334950852900517155081 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P111_replay :
    compactExp2620 momentScalarAmp2622K07P111Input 20 = momentScalarAmp2622K07P111Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P111_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (43 / 200) 0) -
      (momentScalarAmp2622K07P111Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P111Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P111 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P111]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P111 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P111 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P111Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P111Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P111_replay] at h
  simpa only [momentPanelPhase_owner2622K07P111] using h

theorem momentScalarAmp2622K07P111_radius_le :
    (momentScalarAmp2622K07P111Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P111Expected]

def momentScalarGrow2622K07P111Input : RatPair2542 := (momentPanelGrowth2622K07P111 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P111Expected : RatState2542 :=
  ((((669743452740886170404202937256835887860590713111471953938263553199902699010759089575889419098839 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3396002025886491834468005177063665560296960938019 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P111_replay :
    compactExp2620 momentScalarGrow2622K07P111Input 20 = momentScalarGrow2622K07P111Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P111_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (43 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P111Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P111Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P111 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P111]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P111 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P111 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P111Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P111Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P111_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P111] using h

theorem momentScalarGrow2622K07P111_radius_le :
    (momentScalarGrow2622K07P111Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P111Expected]

end ConnesWeilRH.Dev
