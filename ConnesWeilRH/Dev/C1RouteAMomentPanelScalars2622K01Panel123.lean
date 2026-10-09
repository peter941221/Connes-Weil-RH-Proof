import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K01

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K01P123 : ℚ := ((-28492260706231122671294367152091479356010587714525433 : ℚ) / 844716546928022355604346551018683696468128589414400)

def momentPanelGrowth2622K01P123 : ℚ := ((15272773191855252295492506534179001463313291737067411 : ℚ) / 58142752649955264197591109880493461780041007575859200)

theorem momentPanelPhase_owner2622K01P123 :
    (momentPanelPhase2622K01P123 : ℝ) = momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (67 / 200) 0 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P123, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K01P123 :
    (momentPanelGrowth2622K01P123 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2))
      (67 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P123, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K01P123Input : RatPair2542 := (momentPanelPhase2622K01P123 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K01P123Expected : RatState2542 :=
  ((((599474015760885882011759650294714365825744268614315225683181539279208081655093641 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((6079584330913361972916082317275587 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K01P123_replay :
    compactExp2620 momentScalarAmp2622K01P123Input 20 = momentScalarAmp2622K01P123Expected := by
  decide +kernel

theorem momentScalarAmp2622K01P123_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (67 / 200) 0) -
      (momentScalarAmp2622K01P123Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K01P123Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K01P123 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelPhase2622K01P123]
  have h := compactExp_real_error2620 momentPanelPhase2622K01P123 20 hsmall
  change |Real.exp (momentPanelPhase2622K01P123 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K01P123Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K01P123Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K01P123_replay] at h
  simpa only [momentPanelPhase_owner2622K01P123] using h

theorem momentScalarAmp2622K01P123_radius_le :
    (momentScalarAmp2622K01P123Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarAmp2622K01P123Expected]

def momentScalarGrow2622K01P123Input : RatPair2542 := (momentPanelGrowth2622K01P123 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K01P123Expected : RatState2542 :=
  ((((1388826064063201832400349148575804304980837521571145112344379868858686022419373037515320390829579 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1760545752690663471994432168702376065534353645215 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K01P123_replay :
    compactExp2620 momentScalarGrow2622K01P123Input 20 = momentScalarGrow2622K01P123Expected := by
  decide +kernel

theorem momentScalarGrow2622K01P123_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 1).re * (storedWidth 1 ^ 2)) (67 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K01P123Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K01P123Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K01P123 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentPanelGrowth2622K01P123]
  have h := compactExp_real_error2620 momentPanelGrowth2622K01P123 20 hsmall
  change |Real.exp (momentPanelGrowth2622K01P123 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K01P123Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K01P123Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K01P123_replay] at h
  simpa only [momentPanelGrowth_owner2622K01P123] using h

theorem momentScalarGrow2622K01P123_radius_le :
    (momentScalarGrow2622K01P123Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, momentScalarGrow2622K01P123Expected]

end ConnesWeilRH.Dev
