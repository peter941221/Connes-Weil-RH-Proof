import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P038 : ℚ := ((-1882624038685088851932145688262245581747044709211917861 : ℚ) / 44744786065408924655129688456629452323653659761049600)

def momentPanelGrowth2622P038 : ℚ := ((1509378515032560619902246382916475651453500425178093 : ℚ) / 2473134801920887281897797927862085172324023350067200)

theorem momentPanelPhase_owner2622P038 :
    (momentPanelPhase2622P038 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-103 / 200) 0 := by
  norm_num [momentPanelPhase2622P038, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P038 :
    (momentPanelGrowth2622P038 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-103 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P038, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P038Input : RatPair2542 := (momentPanelPhase2622P038 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P038Expected : RatState2542 :=
  ((((569839916713750807596034155563157476453511397336328783459125157700250522624785 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((361194053494453222123190909559 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622P038_replay :
    compactExp2620 momentScalarAmp2622P038Input 20 = momentScalarAmp2622P038Expected := by
  decide +kernel

theorem momentScalarAmp2622P038_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-103 / 200) 0) -
      (momentScalarAmp2622P038Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P038Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P038 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P038]
  have h := compactExp_real_error2620 momentPanelPhase2622P038 20 hsmall
  change |Real.exp (momentPanelPhase2622P038 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P038Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P038Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P038_replay] at h
  simpa only [momentPanelPhase_owner2622P038] using h

theorem momentScalarAmp2622P038_radius_le :
    (momentScalarAmp2622P038Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [momentScalarAmp2622P038Expected]

def momentScalarGrow2622P038Input : RatPair2542 := (momentPanelGrowth2622P038 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P038Expected : RatState2542 :=
  ((((1920095623160278266596587350237974784730414982744233569919308241386244153710156767808534483331 : ℚ) / 1042962419883256876169444192465601618458351817556959360325703910069443225478828393565899456512), 0), ((4984850334743495177774291734358100326148589522059 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P038_replay :
    compactExp2620 momentScalarGrow2622P038Input 20 = momentScalarGrow2622P038Expected := by
  decide +kernel

theorem momentScalarGrow2622P038_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-103 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P038Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P038Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P038 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P038]
  have h := compactExp_real_error2620 momentPanelGrowth2622P038 20 hsmall
  change |Real.exp (momentPanelGrowth2622P038 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P038Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P038Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P038_replay] at h
  simpa only [momentPanelGrowth_owner2622P038] using h

theorem momentScalarGrow2622P038_radius_le :
    (momentScalarGrow2622P038Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P038Expected]

end ConnesWeilRH.Dev
