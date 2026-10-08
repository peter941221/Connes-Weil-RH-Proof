import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K04

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K04P044 : ℚ := ((-127184108590416922232985550260018710229358358288503361 : ℚ) / 3018057970996022764485851510997902415394956011110400)

def momentPanelGrowth2622K04P044 : ℚ := ((99569203433271039089778016580264929878690763463003069 : ℚ) / 184821011792650463009678424128071537837342859250892800)

theorem momentPanelPhase_owner2622K04P044 :
    (momentPanelPhase2622K04P044 : ℝ) = momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-91 / 200) 0 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P044, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K04P044 :
    (momentPanelGrowth2622K04P044 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2))
      (-91 / 200) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P044, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K04P044Input : RatPair2542 := (momentPanelPhase2622K04P044 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K04P044Expected : RatState2542 :=
  ((((133317296188191260896073766711770260461166040209205675678430841236372778681021 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((169006844803895108670875200671 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarAmp2622K04P044_replay :
    compactExp2620 momentScalarAmp2622K04P044Input 20 = momentScalarAmp2622K04P044Expected := by
  decide +kernel

theorem momentScalarAmp2622K04P044_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-91 / 200) 0) -
      (momentScalarAmp2622K04P044Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K04P044Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K04P044 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelPhase2622K04P044]
  have h := compactExp_real_error2620 momentPanelPhase2622K04P044 20 hsmall
  change |Real.exp (momentPanelPhase2622K04P044 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K04P044Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K04P044Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K04P044_replay] at h
  simpa only [momentPanelPhase_owner2622K04P044] using h

theorem momentScalarAmp2622K04P044_radius_le :
    (momentScalarAmp2622K04P044Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 90 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarAmp2622K04P044Expected]

def momentScalarGrow2622K04P044Input : RatPair2542 := (momentPanelGrowth2622K04P044 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K04P044Expected : RatState2542 :=
  ((((915181957751765641329217336901089964430189352706807481597917185088699538540671150597599410079089 : ℚ) / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144), 0), ((4640521448059331572636758935097412078226577932133 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K04P044_replay :
    compactExp2620 momentScalarGrow2622K04P044Input 20 = momentScalarGrow2622K04P044Expected := by
  decide +kernel

theorem momentScalarGrow2622K04P044_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 4).re * (storedWidth 4 ^ 2)) (-91 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K04P044Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K04P044Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K04P044 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentPanelGrowth2622K04P044]
  have h := compactExp_real_error2620 momentPanelGrowth2622K04P044 20 hsmall
  change |Real.exp (momentPanelGrowth2622K04P044 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K04P044Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K04P044Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K04P044_replay] at h
  simpa only [momentPanelGrowth_owner2622K04P044] using h

theorem momentScalarGrow2622K04P044_radius_le :
    (momentScalarGrow2622K04P044Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, momentScalarGrow2622K04P044Expected]

end ConnesWeilRH.Dev
