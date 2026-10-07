import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P085 : ℚ := ((-5500478980840266255857101430781317932337050543885132641 : ℚ) / 182317762064413479974290296366254068317641159947059200)

def momentPanelGrowth2622P085 : ℚ := ((6585427872602692964928022146312983073813727231166557 : ℚ) / 121183605294123476812992098465242173443877144153292800)

theorem momentPanelPhase_owner2622P085 :
    (momentPanelPhase2622P085 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-9 / 200) 0 := by
  norm_num [momentPanelPhase2622P085, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P085 :
    (momentPanelGrowth2622P085 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-9 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P085, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P085Input : RatPair2542 := (momentPanelPhase2622P085 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P085Expected : RatState2542 :=
  ((((168674020301819638976971561072535676197023586046242499334635872840581480760440572515 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((213825875212649311097613716353413019 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P085_replay :
    compactExp2620 momentScalarAmp2622P085Input 20 = momentScalarAmp2622P085Expected := by
  decide +kernel

theorem momentScalarAmp2622P085_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-9 / 200) 0) -
      (momentScalarAmp2622P085Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P085Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P085 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P085]
  have h := compactExp_real_error2620 momentPanelPhase2622P085 20 hsmall
  change |Real.exp (momentPanelPhase2622P085 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P085Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P085Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P085_replay] at h
  simpa only [momentPanelPhase_owner2622P085] using h

theorem momentScalarAmp2622P085_radius_le :
    (momentScalarAmp2622P085Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622P085Expected]

def momentScalarGrow2622P085Input : RatPair2542 := (momentPanelGrowth2622P085 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P085Expected : RatState2542 :=
  ((((1127636935500616193526888959845344426103550507120774913675478548668058289092031677236322794630559 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1429449564045497479970401322720600533176975009663 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622P085_replay :
    compactExp2620 momentScalarGrow2622P085Input 20 = momentScalarGrow2622P085Expected := by
  decide +kernel

theorem momentScalarGrow2622P085_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-9 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P085Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P085Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P085 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P085]
  have h := compactExp_real_error2620 momentPanelGrowth2622P085 20 hsmall
  change |Real.exp (momentPanelGrowth2622P085 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P085Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P085Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P085_replay] at h
  simpa only [momentPanelGrowth_owner2622P085] using h

theorem momentScalarGrow2622P085_radius_le :
    (momentScalarGrow2622P085Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P085Expected]

end ConnesWeilRH.Dev
