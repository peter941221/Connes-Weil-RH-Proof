import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P094 : ℚ := ((-5460783299141505630670534814590804715082443528434867359 : ℚ) / 182317762064413479974290296366254068317641159947059200)

def momentPanelGrowth2622P094 : ℚ := ((6585427872602692964928022146312983073813727231166557 : ℚ) / 121183605294123476812992098465242173443877144153292800)

theorem momentPanelPhase_owner2622P094 :
    (momentPanelPhase2622P094 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (9 / 200) 0 := by
  norm_num [momentPanelPhase2622P094, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P094 :
    (momentPanelGrowth2622P094 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (9 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P094, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P094Input : RatPair2542 := (momentPanelPhase2622P094 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P094Expected : RatState2542 :=
  ((((209703783103588117683941855231381896114049051676742671350638675868184273432112499065 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((66459679988841190649582966056786045 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarAmp2622P094_replay :
    compactExp2620 momentScalarAmp2622P094Input 20 = momentScalarAmp2622P094Expected := by
  decide +kernel

theorem momentScalarAmp2622P094_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (9 / 200) 0) -
      (momentScalarAmp2622P094Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P094Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P094 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P094]
  have h := compactExp_real_error2620 momentPanelPhase2622P094 20 hsmall
  change |Real.exp (momentPanelPhase2622P094 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P094Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P094Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P094_replay] at h
  simpa only [momentPanelPhase_owner2622P094] using h

theorem momentScalarAmp2622P094_radius_le :
    (momentScalarAmp2622P094Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 84 := by
  norm_num [momentScalarAmp2622P094Expected]

def momentScalarGrow2622P094Input : RatPair2542 := (momentPanelGrowth2622P094 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P094Expected : RatState2542 :=
  ((((1127636935500616193526888959845344426103550507120774913675478548668058289092031677236322794630559 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1429449564045497479970401322720600533176975009663 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622P094_replay :
    compactExp2620 momentScalarGrow2622P094Input 20 = momentScalarGrow2622P094Expected := by
  decide +kernel

theorem momentScalarGrow2622P094_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (9 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P094Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P094Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P094 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P094]
  have h := compactExp_real_error2620 momentPanelGrowth2622P094 20 hsmall
  change |Real.exp (momentPanelGrowth2622P094 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P094Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P094Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P094_replay] at h
  simpa only [momentPanelGrowth_owner2622P094] using h

theorem momentScalarGrow2622P094_radius_le :
    (momentScalarGrow2622P094Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P094Expected]

end ConnesWeilRH.Dev
