import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K02

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K02P177 : ℚ := ((-1420655041507664838879098477598643480484542899223 : ℚ) / 11417981541647679048466287755595961091061972992)

def momentPanelGrowth2622K02P177 : ℚ := ((9850997943142131146802006579303078666358354349878733 : ℚ) / 945837045956239613177326111954180426880846187724800)

theorem momentPanelPhase_owner2622K02P177 :
    (momentPanelPhase2622K02P177 : ℝ) = momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (7 / 8) 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P177, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K02P177 :
    (momentPanelGrowth2622K02P177 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2))
      (7 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P177, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K02P177Input : RatPair2542 := (momentPanelPhase2622K02P177 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K02P177Expected : RatState2542 :=
  ((((491458151395982196870791235639322738752169 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K02P177_replay :
    compactExp2620 momentScalarAmp2622K02P177Input 20 = momentScalarAmp2622K02P177Expected := by
  decide +kernel

theorem momentScalarAmp2622K02P177_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (7 / 8) 0) -
      (momentScalarAmp2622K02P177Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K02P177Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K02P177 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelPhase2622K02P177]
  have h := compactExp_real_error2620 momentPanelPhase2622K02P177 20 hsmall
  change |Real.exp (momentPanelPhase2622K02P177 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K02P177Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K02P177Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K02P177_replay] at h
  simpa only [momentPanelPhase_owner2622K02P177] using h

theorem momentScalarAmp2622K02P177_radius_le :
    (momentScalarAmp2622K02P177Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarAmp2622K02P177Expected]

def momentScalarGrow2622K02P177Input : RatPair2542 := (momentPanelGrowth2622K02P177 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K02P177Expected : RatState2542 :=
  ((((8907050549161716026721167638881969820137161732219750164232277830366134383365323665369516607543545399 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((90327326607437675259294464127993476168660236065268467 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K02P177_replay :
    compactExp2620 momentScalarGrow2622K02P177Input 20 = momentScalarGrow2622K02P177Expected := by
  decide +kernel

theorem momentScalarGrow2622K02P177_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 2).re * (storedWidth 2 ^ 2)) (7 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K02P177Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K02P177Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K02P177 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentPanelGrowth2622K02P177]
  have h := compactExp_real_error2620 momentPanelGrowth2622K02P177 20 hsmall
  change |Real.exp (momentPanelGrowth2622K02P177 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K02P177Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K02P177Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K02P177_replay] at h
  simpa only [momentPanelGrowth_owner2622K02P177] using h

theorem momentScalarGrow2622K02P177_radius_le :
    (momentScalarGrow2622K02P177Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 67 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, momentScalarGrow2622K02P177Expected]

end ConnesWeilRH.Dev
