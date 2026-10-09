import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P044 : ℚ := ((-28608879822892139656567075943968864165372996891853039 : ℚ) / 754514492749005691121462877749475603848739002777600)

def momentPanelGrowth2622K01P044 : ℚ := ((20602723460057887823205233531731766133081390724772531 : ℚ) / 46205252948162615752419606032017884459335714812723200)

theorem momentPanelPhase_owner2622K01P044 :
    (momentPanelPhase2622K01P044 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-91 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P044, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P044 :
    (momentPanelGrowth2622K01P044 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (-91 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P044, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P044Input : RatPair2542 := (momentPanelPhase2622K01P044 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P044Expected : RatState2542 :=
  ((((9107335736193683519849600970787296866900387574267578762675709278576881283363857 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((92362699130237188883729824526253 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P044_replay :
    compactExp2620 momentScalarAmp2622K01P044Input 20 = momentScalarAmp2622K01P044Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P044_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-91 / 200) 0) -
      (momentScalarAmp2622K01P044Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P044Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P044 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P044]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P044 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P044 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P044Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P044Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P044_replay] at h
  simpa only [momentPanelPhase_owner2622K01P044] using h

theorem momentScalarAmp2622K01P044_radius_le :
    (momentScalarAmp2622K01P044Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P044Expected]

def momentScalarGrow2622K01P044Input : RatPair2542 := (momentPanelGrowth2622K01P044 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P044Expected : RatState2542 :=
  ((((3336173690283852763710787413143130912358127727427673414226461093950537038672398528592085452617805 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2114550391286912462835726089934484068003419557539 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P044_replay :
    compactExp2620 momentScalarGrow2622K01P044Input 20 = momentScalarGrow2622K01P044Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P044_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (-91 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P044Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P044Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P044 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P044]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P044 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P044 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P044Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P044Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P044_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P044] using h

theorem momentScalarGrow2622K01P044_radius_le :
    (momentScalarGrow2622K01P044Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P044Expected]

end ConnesWeilRH.Dev
