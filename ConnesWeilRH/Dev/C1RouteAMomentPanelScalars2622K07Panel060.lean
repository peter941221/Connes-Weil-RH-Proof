import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K07
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K07P060 : ℚ := ((-34804012912228046102709866915179207525 : ℚ) / 987591088421007136282839559618691072)

def momentPanelGrowth2622K07P060 : ℚ := ((100137291110742106751991679141464675 : ℚ) / 335917267855678965561414375798996992)

theorem momentPanelPhase_owner2622K07P060 :
    (momentPanelPhase2622K07P060 : ℝ) = momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-59 / 200) 0 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P060, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K07P060 :
    (momentPanelGrowth2622K07P060 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2))
      (-59 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P060, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K07P060Input : RatPair2542 := (momentPanelPhase2622K07P060 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K07P060Expected : RatState2542 :=
  ((((529002954756932013699598060259694710898230772502675328997492768123597389899992861 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1341226904848379771109209503008179 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K07P060_replay :
    compactExp2620 momentScalarAmp2622K07P060Input 20 = momentScalarAmp2622K07P060Expected := by
  decide +kernel

theorem momentScalarAmp2622K07P060_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-59 / 200) 0) -
      (momentScalarAmp2622K07P060Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K07P060Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K07P060 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelPhase2622K07P060]
  have h := compactExp_real_error2620 momentPanelPhase2622K07P060 20 hsmall
  change |Real.exp (momentPanelPhase2622K07P060 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K07P060Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K07P060Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K07P060_replay] at h
  simpa only [momentPanelPhase_owner2622K07P060] using h

theorem momentScalarAmp2622K07P060_radius_le :
    (momentScalarAmp2622K07P060Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarAmp2622K07P060Expected]

def momentScalarGrow2622K07P060Input : RatPair2542 := (momentPanelGrowth2622K07P060 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K07P060Expected : RatState2542 :=
  ((((719452727394665475856604617654617422493944870959918824722879905104485189898376606700503545626675 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((456007211219932913950997636604350983367286632387 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K07P060_replay :
    compactExp2620 momentScalarGrow2622K07P060Input 20 = momentScalarGrow2622K07P060Expected := by
  decide +kernel

theorem momentScalarGrow2622K07P060_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 7).re * (storedWidth 7 ^ 2)) (-59 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K07P060Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K07P060Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K07P060 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentPanelGrowth2622K07P060]
  have h := compactExp_real_error2620 momentPanelGrowth2622K07P060 20 hsmall
  change |Real.exp (momentPanelGrowth2622K07P060 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K07P060Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K07P060Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K07P060_replay] at h
  simpa only [momentPanelGrowth_owner2622K07P060] using h

theorem momentScalarGrow2622K07P060_radius_le :
    (momentScalarGrow2622K07P060Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, momentScalarGrow2622K07P060Expected]

end ConnesWeilRH.Dev
