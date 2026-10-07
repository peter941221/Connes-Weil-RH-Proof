import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentScalarAmplitude2620Input : RatPair2542 := (momentPanelPhase2620 / (2 : ℚ) ^ 20, 0)

def momentScalarAmplitude2620Expected : RatState2542 :=
  ((((209703783103588117683941855231381896114049051676742671350638675868184273432112499065 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((66459679988841190649582966056786045 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmplitude2620_replay :
    compactExp2620 momentScalarAmplitude2620Input 20 = momentScalarAmplitude2620Expected := by
  decide +kernel

theorem momentScalarAmplitude2620_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (9 / 200) 0) - (momentScalarAmplitude2620Expected.1.1 : ℝ)| ≤
      (momentScalarAmplitude2620Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2620 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2620]
  have h := compactExp_real_error2620 momentPanelPhase2620 20 hsmall
  change |Real.exp (momentPanelPhase2620 : ℝ) -
    ((compactExp2620 momentScalarAmplitude2620Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmplitude2620Input 20).2 : ℝ) at h
  rw [momentScalarAmplitude2620_replay] at h
  simpa only [momentPanelPhase_owner2620] using h

theorem momentScalarAmplitude2620_radius_le :
    (momentScalarAmplitude2620Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 80 := by
  norm_num [momentScalarAmplitude2620Expected]

end ConnesWeilRH.Dev
