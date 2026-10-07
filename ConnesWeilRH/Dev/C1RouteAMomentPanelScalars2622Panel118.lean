import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P118 : ℚ := ((-5364904026068059373675407071470961272359274053071573903 : ℚ) / 167848895854837541084073816522362866423047427771596800)

def momentPanelGrowth2622P118 : ℚ := ((14789636209823801012204831250202084632767406264981595117 : ℚ) / 63854895069134137022433606665369180700732154452954316800)

theorem momentPanelPhase_owner2622P118 :
    (momentPanelPhase2622P118 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (57 / 200) 0 := by
  norm_num [momentPanelPhase2622P118, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P118 :
    (momentPanelGrowth2622P118 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (57 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P118, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P118Input : RatPair2542 := (momentPanelPhase2622P118 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P118Expected : RatState2542 :=
  ((((438726719451692089602481516086909565867155506164021222886416519628345625851612777 : ℚ) / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384), 0), ((35594825099523430894763383387722359 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P118_replay :
    compactExp2620 momentScalarAmp2622P118Input 20 = momentScalarAmp2622P118Expected := by
  decide +kernel

theorem momentScalarAmp2622P118_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (57 / 200) 0) -
      (momentScalarAmp2622P118Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P118Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P118 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P118]
  have h := compactExp_real_error2620 momentPanelPhase2622P118 20 hsmall
  change |Real.exp (momentPanelPhase2622P118 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P118Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P118Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P118_replay] at h
  simpa only [momentPanelPhase_owner2622P118] using h

theorem momentScalarAmp2622P118_radius_le :
    (momentScalarAmp2622P118Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622P118Expected]

def momentScalarGrow2622P118Input : RatPair2542 := (momentPanelGrowth2622P118 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P118Expected : RatState2542 :=
  ((((1346346820217940315484356449197307449676946848313365263645743908837228762894296337893384035481035 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3413393955566606796728099897295788069808274786081 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P118_replay :
    compactExp2620 momentScalarGrow2622P118Input 20 = momentScalarGrow2622P118Expected := by
  decide +kernel

theorem momentScalarGrow2622P118_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (57 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P118Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P118Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P118 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P118]
  have h := compactExp_real_error2620 momentPanelGrowth2622P118 20 hsmall
  change |Real.exp (momentPanelGrowth2622P118 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P118Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P118Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P118_replay] at h
  simpa only [momentPanelGrowth_owner2622P118] using h

theorem momentScalarGrow2622P118_radius_le :
    (momentScalarGrow2622P118Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P118Expected]

end ConnesWeilRH.Dev
