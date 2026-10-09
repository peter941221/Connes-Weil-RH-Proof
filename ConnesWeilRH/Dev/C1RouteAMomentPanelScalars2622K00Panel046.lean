import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P046 : ℚ := ((-5636504069932361887164135916053302864140538736953937087 : ℚ) / 148118623750870351688324071280693045657692338441420800)

def momentPanelGrowth2622K00P046 : ℚ := ((1299629805901120342105155060620868967931596184331133 : ℚ) / 3021197915919975876224179740130691304694998053683200)

theorem momentPanelPhase_owner2622K00P046 :
    (momentPanelPhase2622K00P046 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-87 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P046, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P046 :
    (momentPanelGrowth2622K00P046 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-87 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P046, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P046Input : RatPair2542 := (momentPanelPhase2622K00P046 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P046Expected : RatState2542 :=
  ((((7940948647374556427595356576338148178296505484189145996886675675414740070124285 : ℚ) / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), 0), ((2516678486758397683058596914011 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarAmp2622K00P046_replay :
    compactExp2620 momentScalarAmp2622K00P046Input 20 = momentScalarAmp2622K00P046Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P046_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-87 / 200) 0) -
      (momentScalarAmp2622K00P046Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P046Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P046 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P046]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P046 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P046 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P046Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P046Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P046_replay] at h
  simpa only [momentPanelPhase_owner2622K00P046] using h

theorem momentScalarAmp2622K00P046_radius_le :
    (momentScalarAmp2622K00P046Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [momentScalarAmp2622K00P046Expected]

def momentScalarGrow2622K00P046Input : RatPair2542 := (momentPanelGrowth2622K00P046 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P046Expected : RatState2542 :=
  ((((3284121588185321776356750830706597828028991305183663144080106128084630183066506222773784547373631 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4163116994598037448784669275771380554552219598707 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P046_replay :
    compactExp2620 momentScalarGrow2622K00P046Input 20 = momentScalarGrow2622K00P046Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P046_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-87 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P046Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P046Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P046 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P046]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P046 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P046 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P046Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P046Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P046_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P046] using h

theorem momentScalarGrow2622K00P046_radius_le :
    (momentScalarGrow2622K00P046Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P046Expected]

end ConnesWeilRH.Dev
