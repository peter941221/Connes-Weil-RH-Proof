import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P063 : ℚ := ((-73252750373874395305627153221804611231861663466450425 : ℚ) / 2264779474748900434621385108897970074334324466909184)

def momentPanelGrowth2622K03P063 : ℚ := ((1503012281935177566650570833937873014883522136158170425 : ℚ) / 7851135734528156228169490180113029356453670391723851776)

theorem momentPanelPhase_owner2622K03P063 :
    (momentPanelPhase2622K03P063 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-53 / 200) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P063, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P063 :
    (momentPanelGrowth2622K03P063 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-53 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P063, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P063Input : RatPair2542 := (momentPanelPhase2622K03P063 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P063Expected : RatState2542 :=
  ((((19170755972731227969101176676880259940326550452331061703139839564652736371615354589 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((24302569942291536045551662978680939 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P063_replay :
    compactExp2620 momentScalarAmp2622K03P063Input 20 = momentScalarAmp2622K03P063Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P063_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-53 / 200) 0) -
      (momentScalarAmp2622K03P063Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P063Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P063 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P063]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P063 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P063 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P063Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P063Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P063_replay] at h
  simpa only [momentPanelPhase_owner2622K03P063] using h

theorem momentScalarAmp2622K03P063_radius_le :
    (momentScalarAmp2622K03P063Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P063Expected]

def momentScalarGrow2622K03P063Input : RatPair2542 := (momentPanelGrowth2622K03P063 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P063Expected : RatState2542 :=
  ((((2586660566464521738688246417944122945711004837334974846096719062107719937815574752467265957688387 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3278981221020801326253901115373208500116738236431 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P063_replay :
    compactExp2620 momentScalarGrow2622K03P063Input 20 = momentScalarGrow2622K03P063Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P063_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-53 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P063Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P063Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P063 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P063]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P063 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P063 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P063Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P063Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P063_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P063] using h

theorem momentScalarGrow2622K03P063_radius_le :
    (momentScalarGrow2622K03P063Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P063Expected]

end ConnesWeilRH.Dev
