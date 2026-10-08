import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P014 : ℚ := ((-125880358399896110764790900390889546767912889067788941 : ℚ) / 1636482204456653599621430692570791123376457279078400)

def momentPanelGrowth2622K04P014 : ℚ := ((137316970688834714058525158080402480118979384805301 : ℚ) / 51809091245226343682415780691016673450693702451200)

theorem momentPanelPhase_owner2622K04P014 :
    (momentPanelPhase2622K04P014 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-151 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P014, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P014 :
    (momentPanelGrowth2622K04P014 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-151 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P014, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P014Input : RatPair2542 := (momentPanelPhase2622K04P014 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P014Expected : RatState2542 :=
  ((((837716800621513839036236357886466918036184688512236209876975133 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2417851640291268554259351 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K04P014_replay :
    compactExp2620 momentScalarAmp2622K04P014Input 20 = momentScalarAmp2622K04P014Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P014_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-151 / 200) 0) -
      (momentScalarAmp2622K04P014Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P014Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P014 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P014]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P014 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P014 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P014Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P014Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P014_replay] at h
  simpa only [momentPanelPhase_owner2622K04P014] using h

theorem momentScalarAmp2622K04P014_radius_le :
    (momentScalarAmp2622K04P014Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P014Expected]

def momentScalarGrow2622K04P014Input : RatPair2542 := (momentPanelGrowth2622K04P014 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P014Expected : RatState2542 :=
  ((((30246196820901121389350669839872894353849525574174443062675160265342739220225335161762929190933049 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((19170756320139863512360633548606864900118820313657 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622K04P014_replay :
    compactExp2620 momentScalarGrow2622K04P014Input 20 = momentScalarGrow2622K04P014Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P014_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-151 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P014Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P014Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P014 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P014]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P014 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P014 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P014Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P014Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P014_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P014] using h

theorem momentScalarGrow2622K04P014_radius_le :
    (momentScalarGrow2622K04P014Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P014Expected]

end ConnesWeilRH.Dev
