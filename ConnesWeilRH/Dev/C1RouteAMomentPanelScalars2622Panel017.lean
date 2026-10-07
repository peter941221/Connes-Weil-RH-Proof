import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P017 : ℚ := ((-15020347191304089605775250902085097057782540874867727 : ℚ) / 231099946402949023940957664173262252483094333358080)

def momentPanelGrowth2622P017 : ℚ := ((33742287277920493873935652669886368515948740400475475837 : ℚ) / 16608018200614706571339209775129451847427538178329804800)

theorem momentPanelPhase_owner2622P017 :
    (momentPanelPhase2622P017 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-29 / 40) 0 := by
  norm_num [momentPanelPhase2622P017, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P017 :
    (momentPanelGrowth2622P017 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-29 / 40) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P017, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P017Input : RatPair2542 := (momentPanelPhase2622P017 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P017Expected : RatState2542 :=
  ((((126653488718580128986342027927414013757394576763876091606843055138291 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2418012201552291363378103 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P017_replay :
    compactExp2620 momentScalarAmp2622P017Input 20 = momentScalarAmp2622P017Expected := by
  decide +kernel

theorem momentScalarAmp2622P017_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-29 / 40) 0) -
      (momentScalarAmp2622P017Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P017Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P017 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P017]
  have h := compactExp_real_error2620 momentPanelPhase2622P017 20 hsmall
  change |Real.exp (momentPanelPhase2622P017 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P017Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P017Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P017_replay] at h
  simpa only [momentPanelPhase_owner2622P017] using h

theorem momentScalarAmp2622P017_radius_le :
    (momentScalarAmp2622P017Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622P017Expected]

def momentScalarGrow2622P017Input : RatPair2542 := (momentPanelGrowth2622P017 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P017Expected : RatState2542 :=
  ((((254547536400466850769813454750419428451555257741699248667271533977126358039598417385498560848569 : ℚ) / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384), 0), ((20651309574158196547834698656931974892963512792695 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P017_replay :
    compactExp2620 momentScalarGrow2622P017Input 20 = momentScalarGrow2622P017Expected := by
  decide +kernel

theorem momentScalarGrow2622P017_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-29 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P017Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P017Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P017 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P017]
  have h := compactExp_real_error2620 momentPanelGrowth2622P017 20 hsmall
  change |Real.exp (momentPanelGrowth2622P017 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P017Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P017Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P017_replay] at h
  simpa only [momentPanelGrowth_owner2622P017] using h

theorem momentScalarGrow2622P017_radius_le :
    (momentScalarGrow2622P017Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P017Expected]

end ConnesWeilRH.Dev
