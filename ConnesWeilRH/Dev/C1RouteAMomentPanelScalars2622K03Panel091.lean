import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P091 : ℚ := ((-219192804056672651484763691298115130167222375001387475 : ℚ) / 7305863997312517325235445018144609279882549790769152)

def momentPanelGrowth2622K03P091 : ℚ := ((2846493705366488756714005773032289597661267585404475 : ℚ) / 190147483054856792814269374666625420292381633058701312)

theorem momentPanelPhase_owner2622K03P091 :
    (momentPanelPhase2622K03P091 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (3 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P091, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P091 :
    (momentPanelGrowth2622K03P091 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (3 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P091, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P091Input : RatPair2542 := (momentPanelPhase2622K03P091 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P091Expected : RatState2542 :=
  ((((199416221858841368945688738017679772338892688671233866192454169517194464865026600585 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((31599665797528560864233011749220293 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K03P091_replay :
    compactExp2620 momentScalarAmp2622K03P091Input 20 = momentScalarAmp2622K03P091Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P091_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (3 / 200) 0) -
      (momentScalarAmp2622K03P091Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P091Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P091 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P091]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P091 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P091 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P091Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P091Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P091_replay] at h
  simpa only [momentPanelPhase_owner2622K03P091] using h

theorem momentScalarAmp2622K03P091_radius_le :
    (momentScalarAmp2622K03P091Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P091Expected]

def momentScalarGrow2622K03P091Input : RatPair2542 := (momentPanelGrowth2622K03P091 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P091Expected : RatState2542 :=
  ((((1084101568988854281819389106604985957286415693476195277160950082525231891126338778675349072833543 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2748523970035052240594153957839216333928369122755 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P091_replay :
    compactExp2620 momentScalarGrow2622K03P091Input 20 = momentScalarGrow2622K03P091Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P091_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (3 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P091Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P091Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P091 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P091]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P091 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P091 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P091Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P091Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P091_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P091] using h

theorem momentScalarGrow2622K03P091_radius_le :
    (momentScalarGrow2622K03P091Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P091Expected]

end ConnesWeilRH.Dev
