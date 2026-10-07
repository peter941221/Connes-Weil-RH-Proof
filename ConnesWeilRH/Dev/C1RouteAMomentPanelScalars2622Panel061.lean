import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P061 : ℚ := ((-5596358253913712512852229173901161375060220019248426097 : ℚ) / 167848895854837541084073816522362866423047427771596800)

def momentPanelGrowth2622P061 : ℚ := ((14789636209823801012204831250202084632767406264981595117 : ℚ) / 63854895069134137022433606665369180700732154452954316800)

theorem momentPanelPhase_owner2622P061 :
    (momentPanelPhase2622P061 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-57 / 200) 0 := by
  norm_num [momentPanelPhase2622P061, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P061 :
    (momentPanelGrowth2622P061 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-57 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P061, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P061Input : RatPair2542 := (momentPanelPhase2622P061 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P061Expected : RatState2542 :=
  ((((7071414401372827696021806025731013726828818692075472178330034959145026243108094729 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((8964367748879925035719661499619405 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P061_replay :
    compactExp2620 momentScalarAmp2622P061Input 20 = momentScalarAmp2622P061Expected := by
  decide +kernel

theorem momentScalarAmp2622P061_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-57 / 200) 0) -
      (momentScalarAmp2622P061Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P061Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P061 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P061]
  have h := compactExp_real_error2620 momentPanelPhase2622P061 20 hsmall
  change |Real.exp (momentPanelPhase2622P061 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P061Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P061Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P061_replay] at h
  simpa only [momentPanelPhase_owner2622P061] using h

theorem momentScalarAmp2622P061_radius_le :
    (momentScalarAmp2622P061Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [momentScalarAmp2622P061Expected]

def momentScalarGrow2622P061Input : RatPair2542 := (momentPanelGrowth2622P061 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P061Expected : RatState2542 :=
  ((((1346346820217940315484356449197307449676946848313365263645743908837228762894296337893384035481035 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3413393955566606796728099897295788069808274786081 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P061_replay :
    compactExp2620 momentScalarGrow2622P061Input 20 = momentScalarGrow2622P061Expected := by
  decide +kernel

theorem momentScalarGrow2622P061_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-57 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P061Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P061Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P061 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P061]
  have h := compactExp_real_error2620 momentPanelGrowth2622P061 20 hsmall
  change |Real.exp (momentPanelGrowth2622P061 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P061Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P061Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P061_replay] at h
  simpa only [momentPanelGrowth_owner2622P061] using h

theorem momentScalarGrow2622P061_radius_le :
    (momentScalarGrow2622P061Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P061Expected]

end ConnesWeilRH.Dev
