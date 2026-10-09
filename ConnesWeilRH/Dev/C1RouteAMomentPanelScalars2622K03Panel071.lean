import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P071 : ℚ := ((-73203917026981882042646873012293805669805181392002825 : ℚ) / 2352469572988754609713606198860947055513680419487744)

def momentPanelGrowth2622K03P071 : ℚ := ((355481173609761661407622606010416155731921293396111475 : ℚ) / 2828928880550828611461272941468774110064208377546801152)

theorem momentPanelPhase_owner2622K03P071 :
    (momentPanelPhase2622K03P071 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-37 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P071, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P071 :
    (momentPanelGrowth2622K03P071 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-37 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P071, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P071Input : RatPair2542 := (momentPanelPhase2622K03P071 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P071Expected : RatState2542 :=
  ((((16338252572137309796922254913563591462228443243959004235607011149821815355673543295 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((82847241288142911661459300415952977 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P071_replay :
    compactExp2620 momentScalarAmp2622K03P071Input 20 = momentScalarAmp2622K03P071Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P071_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-37 / 200) 0) -
      (momentScalarAmp2622K03P071Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P071Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P071 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P071]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P071 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P071 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P071Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P071Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P071_replay] at h
  simpa only [momentPanelPhase_owner2622K03P071] using h

theorem momentScalarAmp2622K03P071_radius_le :
    (momentScalarAmp2622K03P071Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P071Expected]

def momentScalarGrow2622K03P071Input : RatPair2542 := (momentPanelGrowth2622K03P071 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P071Expected : RatState2542 :=
  ((((1210993326447717878114781011053991514651023682480739559580341664541172650717384882614145358555591 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((383779058294628219493339088228314522629835924795 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K03P071_replay :
    compactExp2620 momentScalarGrow2622K03P071Input 20 = momentScalarGrow2622K03P071Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P071_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-37 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P071Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P071Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P071 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P071]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P071 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P071 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P071Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P071Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P071_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P071] using h

theorem momentScalarGrow2622K03P071_radius_le :
    (momentScalarGrow2622K03P071Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P071Expected]

end ConnesWeilRH.Dev
