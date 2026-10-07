import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P053 : ℚ := ((-1873484897725442832319355182882745703479066444105720331 : ℚ) / 52783045070728890705249955036569008931761288747417600)

def momentPanelGrowth2622P053 : ℚ := ((18270416743879523076810146916811571733063795277151035277 : ℚ) / 56704863683902027220851629542512945097820418469579980800)

theorem momentPanelPhase_owner2622P053 :
    (momentPanelPhase2622P053 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-73 / 200) 0 := by
  norm_num [momentPanelPhase2622P053, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P053 :
    (momentPanelGrowth2622P053 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-73 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P053, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P053Input : RatPair2542 := (momentPanelPhase2622P053 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P053Expected : RatState2542 :=
  ((((410857776479828119593854412646743017618858846113596153830787854920480613801113963 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((260420869125751364268255324489093 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622P053_replay :
    compactExp2620 momentScalarAmp2622P053Input 20 = momentScalarAmp2622P053Expected := by
  decide +kernel

theorem momentScalarAmp2622P053_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-73 / 200) 0) -
      (momentScalarAmp2622P053Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P053Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P053 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P053]
  have h := compactExp_real_error2620 momentPanelPhase2622P053 20 hsmall
  change |Real.exp (momentPanelPhase2622P053 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P053Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P053Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P053_replay] at h
  simpa only [momentPanelPhase_owner2622P053] using h

theorem momentScalarAmp2622P053_radius_le :
    (momentScalarAmp2622P053Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [momentScalarAmp2622P053Expected]

def momentScalarGrow2622P053Input : RatPair2542 := (momentPanelGrowth2622P053 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P053Expected : RatState2542 :=
  ((((2948011235989739030288402314420948100719992211369659427495875782168113764435689313804164676353095 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3737047064477994033218136626165351842937583035329 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P053_replay :
    compactExp2620 momentScalarGrow2622P053Input 20 = momentScalarGrow2622P053Expected := by
  decide +kernel

theorem momentScalarGrow2622P053_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-73 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P053Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P053Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P053 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P053]
  have h := compactExp_real_error2620 momentPanelGrowth2622P053 20 hsmall
  change |Real.exp (momentPanelGrowth2622P053 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P053Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P053Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P053_replay] at h
  simpa only [momentPanelGrowth_owner2622P053] using h

theorem momentScalarGrow2622P053_radius_le :
    (momentScalarGrow2622P053Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P053Expected]

end ConnesWeilRH.Dev
