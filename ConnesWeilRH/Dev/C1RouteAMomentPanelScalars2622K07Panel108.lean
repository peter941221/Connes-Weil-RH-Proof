import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P108 : ℚ := ((-30891465240408410992368203748897672325 : ℚ) / 1044706353864890240196675019240112128)

def momentPanelGrowth2622K07P108 : ℚ := ((255574690729006231024973451188905500025 : ℚ) / 1256296791285839647516763469367606247424)

theorem momentPanelPhase_owner2622K07P108 :
    (momentPanelPhase2622K07P108 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (37 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P108, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P108 :
    (momentPanelGrowth2622K07P108 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (37 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P108, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P108Input : RatPair2542 := (momentPanelPhase2622K07P108 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P108Expected : RatState2542 :=
  ((((76852735293793569237643736474805277685049468304186043008116196666844424837531079909 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((194850326691573907620779018322875069 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K07P108_replay :
    compactExp2620 momentScalarAmp2622K07P108Input 20 = momentScalarAmp2622K07P108Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P108_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (37 / 200) 0) -
      (momentScalarAmp2622K07P108Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P108Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P108 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P108]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P108 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P108 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P108Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P108Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P108_replay] at h
  simpa only [momentPanelPhase_owner2622K07P108] using h

theorem momentScalarAmp2622K07P108_radius_le :
    (momentScalarAmp2622K07P108Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P108Expected]

def momentScalarGrow2622K07P108Input : RatPair2542 := (momentPanelGrowth2622K07P108 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P108Expected : RatState2542 :=
  ((((654469335331636865957810095030365641764068429987672966569326657428634142543413351928451364768161 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((3318553139221603079932665866327464683139085453617 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K07P108_replay :
    compactExp2620 momentScalarGrow2622K07P108Input 20 = momentScalarGrow2622K07P108Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P108_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (37 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P108Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P108Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P108 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P108]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P108 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P108 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P108Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P108Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P108_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P108] using h

theorem momentScalarGrow2622K07P108_radius_le :
    (momentScalarGrow2622K07P108Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P108Expected]

end ConnesWeilRH.Dev
