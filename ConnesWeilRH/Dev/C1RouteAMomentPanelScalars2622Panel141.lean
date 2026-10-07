import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P141 : ℚ := ((-1771130054642168443577066393528461967392786648228082139 : ℚ) / 44744786065408924655129688456629452323653659761049600)

def momentPanelGrowth2622P141 : ℚ := ((1509378515032560619902246382916475651453500425178093 : ℚ) / 2473134801920887281897797927862085172324023350067200)

theorem momentPanelPhase_owner2622P141 :
    (momentPanelPhase2622P141 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (103 / 200) 0 := by
  norm_num [momentPanelPhase2622P141, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P141 :
    (momentPanelGrowth2622P141 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (103 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P141, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P141Input : RatPair2542 := (momentPanelPhase2622P141 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P141Expected : RatState2542 :=
  ((((13770427735203792845644295136761141134429439890257266243623593383954083366896921 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2182094046027816810531759293461 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622P141_replay :
    compactExp2620 momentScalarAmp2622P141Input 20 = momentScalarAmp2622P141Expected := by
  decide +kernel

theorem momentScalarAmp2622P141_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (103 / 200) 0) -
      (momentScalarAmp2622P141Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P141Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P141 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P141]
  have h := compactExp_real_error2620 momentPanelPhase2622P141 20 hsmall
  change |Real.exp (momentPanelPhase2622P141 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P141Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P141Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P141_replay] at h
  simpa only [momentPanelPhase_owner2622P141] using h

theorem momentScalarAmp2622P141_radius_le :
    (momentScalarAmp2622P141Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 89 := by
  norm_num [momentScalarAmp2622P141Expected]

def momentScalarGrow2622P141Input : RatPair2542 := (momentPanelGrowth2622P141 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P141Expected : RatState2542 :=
  ((((1920095623160278266596587350237974784730414982744233569919308241386244153710156767808534483331 : ℚ) / 1042962419883256876169444192465601618458351817556959360325703910069443225478828393565899456512), 0), ((4984850334743495177774291734358100326148589522059 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P141_replay :
    compactExp2620 momentScalarGrow2622P141Input 20 = momentScalarGrow2622P141Expected := by
  decide +kernel

theorem momentScalarGrow2622P141_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (103 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P141Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P141Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P141 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P141]
  have h := compactExp_real_error2620 momentPanelGrowth2622P141 20 hsmall
  change |Real.exp (momentPanelGrowth2622P141 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P141Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P141Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P141_replay] at h
  simpa only [momentPanelGrowth_owner2622P141] using h

theorem momentScalarGrow2622P141_radius_le :
    (momentScalarGrow2622P141Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P141Expected]

end ConnesWeilRH.Dev
