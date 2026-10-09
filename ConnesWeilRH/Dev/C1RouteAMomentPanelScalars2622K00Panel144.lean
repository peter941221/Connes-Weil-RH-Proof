import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P144 : ℚ := ((-1770435848964244778688870023519401969385681438294427553 : ℚ) / 42808296395945478288509806053280377322609549141606400)

def momentPanelGrowth2622K00P144 : ℚ := ((41624730863388413161156100735530965301429349941273037 : ℚ) / 59252473412226465654110953678889680485957002644684800)

theorem momentPanelPhase_owner2622K00P144 :
    (momentPanelPhase2622K00P144 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (109 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P144, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P144 :
    (momentPanelGrowth2622K00P144 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (109 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P144, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P144Input : RatPair2542 := (momentPanelPhase2622K00P144 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P144Expected : RatState2542 :=
  ((((2335331134452491774446977275429662931510392653432039680858791887788313532800257 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2960503096164697697581000086153 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P144_replay :
    compactExp2620 momentScalarAmp2622K00P144Input 20 = momentScalarAmp2622K00P144Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P144_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (109 / 200) 0) -
      (momentScalarAmp2622K00P144Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P144Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P144 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P144]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P144 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P144 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P144Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P144Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P144_replay] at h
  simpa only [momentPanelPhase_owner2622K00P144] using h

theorem momentScalarAmp2622K00P144_radius_le :
    (momentScalarAmp2622K00P144Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [momentScalarAmp2622K00P144Expected]

def momentScalarGrow2622K00P144Input : RatPair2542 := (momentPanelGrowth2622K00P144 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P144Expected : RatState2542 :=
  ((((1078026729674004543276798822487000757477471289198683040305769293169149057171849772843122674516463 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((5466241261601405623544427341073733232345669027105 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P144_replay :
    compactExp2620 momentScalarGrow2622K00P144Input 20 = momentScalarGrow2622K00P144Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P144_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (109 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P144Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P144Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P144 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P144]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P144 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P144 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P144Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P144Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P144_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P144] using h

theorem momentScalarGrow2622K00P144_radius_le :
    (momentScalarGrow2622K00P144Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P144Expected]

end ConnesWeilRH.Dev
