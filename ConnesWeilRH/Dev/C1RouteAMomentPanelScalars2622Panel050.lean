import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P050 : ℚ := ((-1875988921802919199876444842840620402641094993003764877 : ℚ) / 51394618515264532932956454445488540063088152831590400)

def momentPanelGrowth2622P050 : ℚ := ((122300795414469687075850717069871731477583430401237 : ℚ) / 335688657324441764024908860014521256077222005964800)

theorem momentPanelPhase_owner2622P050 :
    (momentPanelPhase2622P050 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-79 / 200) 0 := by
  norm_num [momentPanelPhase2622P050, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P050 :
    (momentPanelGrowth2622P050 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-79 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P050, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P050Input : RatPair2542 := (momentPanelPhase2622P050 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P050Expected : RatState2542 :=
  ((((300005234804368699005974775712589693783850409060824911535688934604158374655309831 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((380315057190633689114854756860613 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P050_replay :
    compactExp2620 momentScalarAmp2622P050Input 20 = momentScalarAmp2622P050Expected := by
  decide +kernel

theorem momentScalarAmp2622P050_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-79 / 200) 0) -
      (momentScalarAmp2622P050Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P050Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P050 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P050]
  have h := compactExp_real_error2620 momentPanelPhase2622P050 20 hsmall
  change |Real.exp (momentPanelPhase2622P050 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P050Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P050Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P050_replay] at h
  simpa only [momentPanelPhase_owner2622P050] using h

theorem momentScalarAmp2622P050_radius_le :
    (momentScalarAmp2622P050Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [momentScalarAmp2622P050Expected]

def momentScalarGrow2622P050Input : RatPair2542 := (momentPanelGrowth2622P050 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P050Expected : RatState2542 :=
  ((((1537426209331312617478440655335024368104427245299398447711468096347634633343048530905893385888195 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((974459289956485479210233645096239000367900494541 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622P050_replay :
    compactExp2620 momentScalarGrow2622P050Input 20 = momentScalarGrow2622P050Expected := by
  decide +kernel

theorem momentScalarGrow2622P050_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-79 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P050Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P050Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P050 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P050]
  have h := compactExp_real_error2620 momentPanelGrowth2622P050 20 hsmall
  change |Real.exp (momentPanelGrowth2622P050 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P050Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P050Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P050_replay] at h
  simpa only [momentPanelGrowth_owner2622P050] using h

theorem momentScalarGrow2622P050_radius_le :
    (momentScalarGrow2622P050Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P050Expected]

end ConnesWeilRH.Dev
