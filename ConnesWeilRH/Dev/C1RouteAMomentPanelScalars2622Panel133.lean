import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P133 : ℚ := ((-5324758210049409999363500329318819783278955335366062913 : ℚ) / 148118623750870351688324071280693045657692338441420800)

def momentPanelGrowth2622P133 : ℚ := ((1299629805901120342105155060620868967931596184331133 : ℚ) / 3021197915919975876224179740130691304694998053683200)

theorem momentPanelPhase_owner2622P133 :
    (momentPanelPhase2622P133 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (87 / 200) 0 := by
  norm_num [momentPanelPhase2622P133, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P133 :
    (momentPanelGrowth2622P133 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (87 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P133, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P133Input : RatPair2542 := (momentPanelPhase2622P133 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P133Expected : RatState2542 :=
  ((((260611581725464594827732404581406966131713984556213009385617652544499231769241021 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((82593938896793612912567944712283 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622P133_replay :
    compactExp2620 momentScalarAmp2622P133Input 20 = momentScalarAmp2622P133Expected := by
  decide +kernel

theorem momentScalarAmp2622P133_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (87 / 200) 0) -
      (momentScalarAmp2622P133Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P133Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P133 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P133]
  have h := compactExp_real_error2620 momentPanelPhase2622P133 20 hsmall
  change |Real.exp (momentPanelPhase2622P133 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P133Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P133Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P133_replay] at h
  simpa only [momentPanelPhase_owner2622P133] using h

theorem momentScalarAmp2622P133_radius_le :
    (momentScalarAmp2622P133Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [momentScalarAmp2622P133Expected]

def momentScalarGrow2622P133Input : RatPair2542 := (momentPanelGrowth2622P133 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P133Expected : RatState2542 :=
  ((((3284121588185321776356750830706597828028991305183663144080106128084630183066506222773784547373631 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4163116994598037448784669275771380554552219598707 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P133_replay :
    compactExp2620 momentScalarGrow2622P133Input 20 = momentScalarGrow2622P133Expected := by
  decide +kernel

theorem momentScalarGrow2622P133_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (87 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P133Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P133Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P133 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P133]
  have h := compactExp_real_error2620 momentPanelGrowth2622P133 20 hsmall
  change |Real.exp (momentPanelGrowth2622P133 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P133Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P133Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P133_replay] at h
  simpa only [momentPanelGrowth_owner2622P133] using h

theorem momentScalarGrow2622P133_radius_le :
    (momentScalarGrow2622P133Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P133Expected]

end ConnesWeilRH.Dev
