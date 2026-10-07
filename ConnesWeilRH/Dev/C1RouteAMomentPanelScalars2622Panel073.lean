import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P073 : ℚ := ((-5551568894679067934934365270779616012632040302357541673 : ℚ) / 177714031906821135781948689143197776805724972436684800)

def momentPanelGrowth2622P073 : ℚ := ((9500819302699793819936465330369519877616457359208624797 : ℚ) / 71783724139358951716553372343459105617743045490166988800)

theorem momentPanelPhase_owner2622P073 :
    (momentPanelPhase2622P073 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-33 / 200) 0 := by
  norm_num [momentPanelPhase2622P073, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P073 :
    (momentPanelGrowth2622P073 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-33 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P073, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P073Input : RatPair2542 := (momentPanelPhase2622P073 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P073Expected : RatState2542 :=
  ((((57912248599366587994655743823442243989766623298904266298875620372973099760356778901 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((73414683809657071992982848441416573 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P073_replay :
    compactExp2620 momentScalarAmp2622P073Input 20 = momentScalarAmp2622P073Expected := by
  decide +kernel

theorem momentScalarAmp2622P073_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-33 / 200) 0) -
      (momentScalarAmp2622P073Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P073Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P073 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P073]
  have h := compactExp_real_error2620 momentPanelPhase2622P073 20 hsmall
  change |Real.exp (momentPanelPhase2622P073 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P073Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P073Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P073_replay] at h
  simpa only [momentPanelPhase_owner2622P073] using h

theorem momentScalarAmp2622P073_radius_le :
    (momentScalarAmp2622P073Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622P073Expected]

def momentScalarGrow2622P073Input : RatPair2542 := (momentPanelGrowth2622P073 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P073Expected : RatState2542 :=
  ((((2438254081155978503196257569663138343957517940369671464952842829630788032122098065927701395617097 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3090853859352434194982972467490515668803850113559 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P073_replay :
    compactExp2620 momentScalarGrow2622P073Input 20 = momentScalarGrow2622P073Expected := by
  decide +kernel

theorem momentScalarGrow2622P073_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-33 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P073Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P073Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P073 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P073]
  have h := compactExp_real_error2620 momentPanelGrowth2622P073 20 hsmall
  change |Real.exp (momentPanelGrowth2622P073 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P073Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P073Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P073_replay] at h
  simpa only [momentPanelGrowth_owner2622P073] using h

theorem momentScalarGrow2622P073_radius_le :
    (momentScalarGrow2622P073Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P073Expected]

end ConnesWeilRH.Dev
