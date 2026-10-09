import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P116 : ℚ := ((-72897413359215896514741330049823690733731590831149575 : ℚ) / 2264779474748900434621385108897970074334324466909184)

def momentPanelGrowth2622K03P116 : ℚ := ((1503012281935177566650570833937873014883522136158170425 : ℚ) / 7851135734528156228169490180113029356453670391723851776)

theorem momentPanelPhase_owner2622K03P116 :
    (momentPanelPhase2622K03P116 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (53 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P116, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P116 :
    (momentPanelGrowth2622K03P116 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (53 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P116, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P116Input : RatPair2542 := (momentPanelPhase2622K03P116 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P116Expected : RatState2542 :=
  ((((22427389365997406711494601895907480555249745503646146259939119412160081537513231843 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((28430966306363486748480604895675591 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P116_replay :
    compactExp2620 momentScalarAmp2622K03P116Input 20 = momentScalarAmp2622K03P116Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P116_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (53 / 200) 0) -
      (momentScalarAmp2622K03P116Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P116Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P116 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P116]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P116 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P116 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P116Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P116Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P116_replay] at h
  simpa only [momentPanelPhase_owner2622K03P116] using h

theorem momentScalarAmp2622K03P116_radius_le :
    (momentScalarAmp2622K03P116Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P116Expected]

def momentScalarGrow2622K03P116Input : RatPair2542 := (momentPanelGrowth2622K03P116 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P116Expected : RatState2542 :=
  ((((2586660566464521738688246417944122945711004837334974846096719062107719937815574752467265957688387 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3278981221020801326253901115373208500116738236431 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P116_replay :
    compactExp2620 momentScalarGrow2622K03P116Input 20 = momentScalarGrow2622K03P116Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P116_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (53 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P116Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P116Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P116 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P116]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P116 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P116 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P116Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P116Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P116_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P116] using h

theorem momentScalarGrow2622K03P116_radius_le :
    (momentScalarGrow2622K03P116Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P116Expected]

end ConnesWeilRH.Dev
