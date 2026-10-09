import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P028 : ℚ := ((-5649632214169117261139261857758935657902790341903319643 : ℚ) / 113590647568927770245762017107770859318320932113612800)

def momentPanelGrowth2622K00P028 : ℚ := ((1813403265181753366859342204914042109063325611554829797 : ℚ) / 1802915270600326828503494689411460090624213022198988800)

theorem momentPanelPhase_owner2622K00P028 :
    (momentPanelPhase2622K00P028 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-123 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P028, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P028 :
    (momentPanelGrowth2622K00P028 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-123 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P028, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P028Input : RatPair2542 := (momentPanelPhase2622K00P028 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P028Expected : RatState2542 :=
  ((((536034447097020195176158741578133067809269184798320806327726514214863464275 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((681954471725291231592861663 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P028_replay :
    compactExp2620 momentScalarAmp2622K00P028Input 20 = momentScalarAmp2622K00P028Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P028_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-123 / 200) 0) -
      (momentScalarAmp2622K00P028Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P028Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P028 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P028]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P028 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P028 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P028Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P028Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P028_replay] at h
  simpa only [momentPanelPhase_owner2622K00P028] using h

theorem momentScalarAmp2622K00P028_radius_le :
    (momentScalarAmp2622K00P028Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 93 := by
  norm_num [momentScalarAmp2622K00P028Expected]

def momentScalarGrow2622K00P028Input : RatPair2542 := (momentPanelGrowth2622K00P028 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P028Expected : RatState2542 :=
  ((((1460022333784145060088436916344238421005637904518950259004579532990423886644998325444215355120231 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((7403185649769892114208045192967721259541304466279 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P028_replay :
    compactExp2620 momentScalarGrow2622K00P028Input 20 = momentScalarGrow2622K00P028Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P028_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-123 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P028Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P028Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P028 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P028]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P028 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P028 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P028Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P028Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P028_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P028] using h

theorem momentScalarGrow2622K00P028_radius_le :
    (momentScalarGrow2622K00P028Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P028Expected]

end ConnesWeilRH.Dev
