import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P178 : ℚ := ((-218810233808912803820498814898636578269219481739028025 : ℚ) / 1584085087162032400468018898060361257929573885018112)

def momentPanelGrowth2622K03P178 : ℚ := ((1626310159652115209080778131662945663506479131318453475 : ℚ) / 131603381217474149168325269480092913232514115218440192)

theorem momentPanelPhase_owner2622K03P178 :
    (momentPanelPhase2622K03P178 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (177 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P178, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P178 :
    (momentPanelGrowth2622K03P178 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (177 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P178, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P178Input : RatPair2542 := (momentPanelPhase2622K03P178 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P178Expected : RatState2542 :=
  ((((273689485266336057860010138329282899 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P178_replay :
    compactExp2620 momentScalarAmp2622K03P178Input 20 = momentScalarAmp2622K03P178Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P178_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (177 / 200) 0) -
      (momentScalarAmp2622K03P178Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P178Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P178 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P178]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P178 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P178 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P178Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P178Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P178_replay] at h
  simpa only [momentPanelPhase_owner2622K03P178] using h

theorem momentScalarAmp2622K03P178_radius_le :
    (momentScalarAmp2622K03P178Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P178Expected]

def momentScalarGrow2622K03P178Input : RatPair2542 := (momentPanelGrowth2622K03P178 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P178Expected : RatState2542 :=
  ((((497122265141937110878029460275318247384632739938735088027319000444234985665378527592134945360103802267 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((78771238885134698160679881852078415591281043045845101 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K03P178_replay :
    compactExp2620 momentScalarGrow2622K03P178Input 20 = momentScalarGrow2622K03P178Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P178_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (177 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P178Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P178Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P178 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P178]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P178 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P178 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P178Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P178Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P178_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P178] using h

theorem momentScalarGrow2622K03P178_radius_le :
    (momentScalarGrow2622K03P178Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 66 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P178Expected]

end ConnesWeilRH.Dev
