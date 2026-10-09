import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P140 : ℚ := ((-1771453678457326555061632232738478955163407555421409257 : ℚ) / 45365924261274558395366254510533872607007431091814400)

def momentPanelGrowth2622K00P140 : ℚ := ((72902432628809651017816355233940216141072483844027185671 : ℚ) / 125015938902358412138355132980787952943673402980722278400)

theorem momentPanelPhase_owner2622K00P140 :
    (momentPanelPhase2622K00P140 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (101 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P140, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P140 :
    (momentPanelGrowth2622K00P140 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (101 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P140, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P140Input : RatPair2542 := (momentPanelPhase2622K00P140 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P140Expected : RatState2542 :=
  ((((11754094328912590644098628512483355793933237742196705600291448911602575806135597 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((29801281634796947655897294958829 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P140_replay :
    compactExp2620 momentScalarAmp2622K00P140Input 20 = momentScalarAmp2622K00P140Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P140_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (101 / 200) 0) -
      (momentScalarAmp2622K00P140Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P140Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P140 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P140]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P140 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P140 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P140Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P140Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P140_replay] at h
  simpa only [momentPanelPhase_owner2622K00P140] using h

theorem momentScalarAmp2622K00P140_radius_le :
    (momentScalarAmp2622K00P140Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [momentScalarAmp2622K00P140Expected]

def momentScalarGrow2622K00P140Input : RatPair2542 := (momentPanelGrowth2622K00P140 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P140Expected : RatState2542 :=
  ((((956743062437738053337283382833353628639916582149843273676103835625199074183779156723577942489115 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((4851260971518593687137408279039211150609892145581 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P140_replay :
    compactExp2620 momentScalarGrow2622K00P140Input 20 = momentScalarGrow2622K00P140Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P140_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (101 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P140Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P140Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P140 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P140]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P140 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P140 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P140Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P140Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P140_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P140] using h

theorem momentScalarGrow2622K00P140_radius_le :
    (momentScalarGrow2622K00P140Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P140Expected]

end ConnesWeilRH.Dev
