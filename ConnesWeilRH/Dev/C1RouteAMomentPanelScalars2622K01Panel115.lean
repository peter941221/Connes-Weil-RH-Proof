import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P115 : ℚ := ((-85508134940001973981188871328337023520424912581009723 : ℚ) / 2668881822975509679584941848572083430278917049548800)

def momentPanelGrowth2622K01P115 : ℚ := ((11716725003590817813704521136112875862953319757546051 : ℚ) / 64625311670225733977357844753733068689491442742067200)

theorem momentPanelPhase_owner2622K01P115 :
    (momentPanelPhase2622K01P115 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (51 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P115, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P115 :
    (momentPanelGrowth2622K01P115 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (51 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P115, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P115Input : RatPair2542 := (momentPanelPhase2622K01P115 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P115Expected : RatState2542 :=
  ((((26017486344866932433847669742338573079082078206695951798221027443660317147405555909 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((32982089926740139316884414941303101 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P115_replay :
    compactExp2620 momentScalarAmp2622K01P115Input 20 = momentScalarAmp2622K01P115Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P115_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (51 / 200) 0) -
      (momentScalarAmp2622K01P115Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P115Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P115 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P115]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P115 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P115 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P115Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P115Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P115_replay] at h
  simpa only [momentPanelPhase_owner2622K01P115] using h

theorem momentScalarAmp2622K01P115_radius_le :
    (momentScalarAmp2622K01P115Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P115Expected]

def momentScalarGrow2622K01P115Input : RatPair2542 := (momentPanelGrowth2622K01P115 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P115Expected : RatState2542 :=
  ((((2560573522520586667412583538226413378128576488588131789912001870468590674224222798403085385786947 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3245912001522283202826821841154332568627514062845 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K01P115_replay :
    compactExp2620 momentScalarGrow2622K01P115Input 20 = momentScalarGrow2622K01P115Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P115_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (51 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P115Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P115Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P115 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P115]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P115 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P115 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P115Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P115Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P115_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P115] using h

theorem momentScalarGrow2622K01P115_radius_le :
    (momentScalarGrow2622K01P115Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P115Expected]

end ConnesWeilRH.Dev
