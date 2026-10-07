import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P098 : ℚ := ((-1814445373140034474101419589616604586957240341607127341 : ℚ) / 60455928666716131025819300408329494784954934598041600)

def momentPanelGrowth2622P098 : ℚ := ((17766762200709479753538110740626802596040323363216826231 : ℚ) / 224675187488838683042070075341899023447879072111552102400)

theorem momentPanelPhase_owner2622P098 :
    (momentPanelPhase2622P098 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (17 / 200) 0 := by
  norm_num [momentPanelPhase2622P098, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P098 :
    (momentPanelGrowth2622P098 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (17 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P098, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P098Input : RatPair2542 := (momentPanelPhase2622P098 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P098Expected : RatState2542 :=
  ((((49339030915972807109276223791940590759773136071473348153664639250369297470089731177 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((250185769422537251309880762507951197 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P098_replay :
    compactExp2620 momentScalarAmp2622P098Input 20 = momentScalarAmp2622P098Expected := by
  decide +kernel

theorem momentScalarAmp2622P098_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (17 / 200) 0) -
      (momentScalarAmp2622P098Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P098Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P098 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P098]
  have h := compactExp_real_error2620 momentPanelPhase2622P098 20 hsmall
  change |Real.exp (momentPanelPhase2622P098 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P098Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P098Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P098_replay] at h
  simpa only [momentPanelPhase_owner2622P098] using h

theorem momentScalarAmp2622P098_radius_le :
    (momentScalarAmp2622P098Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622P098Expected]

def momentScalarGrow2622P098Input : RatPair2542 := (momentPanelGrowth2622P098 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P098Expected : RatState2542 :=
  ((((2311753659649769016907138838867016532036597973326115606871401471038439098954520247637461890240631 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2930495693233770284630822534797870139683042336865 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P098_replay :
    compactExp2620 momentScalarGrow2622P098Input 20 = momentScalarGrow2622P098Expected := by
  decide +kernel

theorem momentScalarGrow2622P098_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (17 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P098Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P098Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P098 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P098]
  have h := compactExp_real_error2620 momentPanelGrowth2622P098 20 hsmall
  change |Real.exp (momentPanelGrowth2622P098 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P098Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P098Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P098_replay] at h
  simpa only [momentPanelGrowth_owner2622P098] using h

theorem momentScalarGrow2622P098_radius_le :
    (momentScalarGrow2622P098Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P098Expected]

end ConnesWeilRH.Dev
