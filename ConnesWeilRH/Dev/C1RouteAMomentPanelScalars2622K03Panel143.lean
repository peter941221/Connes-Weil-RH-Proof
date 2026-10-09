import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P143 : ℚ := ((-72799721247169773726229160775815734612482356474742425 : ℚ) / 1738638885309775384068058569120108187258188751437824)

def momentPanelGrowth2622K03P143 : ℚ := ((185819416679490515623777571664344879920740833948995425 : ℚ) / 286494603555735904979605216275593214403292045064011776)

theorem momentPanelPhase_owner2622K03P143 :
    (momentPanelPhase2622K03P143 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (107 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P143, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P143 :
    (momentPanelGrowth2622K03P143 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (107 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P143, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P143Input : RatPair2542 := (momentPanelPhase2622K03P143 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P143Expected : RatState2542 :=
  ((((1396244537088441778031078166976332868313677567216925150936694153529045132187513 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((221252915289415459677092491633 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K03P143_replay :
    compactExp2620 momentScalarAmp2622K03P143Input 20 = momentScalarAmp2622K03P143Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P143_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (107 / 200) 0) -
      (momentScalarAmp2622K03P143Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P143Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P143 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P143]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P143 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P143 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P143Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P143Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P143_replay] at h
  simpa only [momentPanelPhase_owner2622K03P143] using h

theorem momentScalarAmp2622K03P143_radius_le :
    (momentScalarAmp2622K03P143Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P143Expected]

def momentScalarGrow2622K03P143Input : RatPair2542 := (momentPanelGrowth2622K03P143 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P143Expected : RatState2542 :=
  ((((1021458041296284873031176987472327250837328975641388226054913580038712212815027091309640656409907 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((5179404392907746099479986182168855610006929562363 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P143_replay :
    compactExp2620 momentScalarGrow2622K03P143Input 20 = momentScalarGrow2622K03P143Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P143_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (107 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P143Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P143Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P143 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P143]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P143 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P143 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P143Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P143Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P143_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P143] using h

theorem momentScalarGrow2622K03P143_radius_le :
    (momentScalarGrow2622K03P143Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P143Expected]

end ConnesWeilRH.Dev
