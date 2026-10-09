import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P129 : ℚ := ((-1777765171524338095632767238950087146498736364436235123 : ℚ) / 51394618515264532932956454445488540063088152831590400)

def momentPanelGrowth2622K00P129 : ℚ := ((122300795414469687075850717069871731477583430401237 : ℚ) / 335688657324441764024908860014521256077222005964800)

theorem momentPanelPhase_owner2622K00P129 :
    (momentPanelPhase2622K00P129 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (79 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P129, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P129 :
    (momentPanelGrowth2622K00P129 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (79 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P129, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P129Input : RatPair2542 := (momentPanelPhase2622K00P129 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P129Expected : RatState2542 :=
  ((((2028329696734395240451961866859064074054407982415583876960196627799107704693989601 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1285649090347383818224436713648233 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K00P129_replay :
    compactExp2620 momentScalarAmp2622K00P129Input 20 = momentScalarAmp2622K00P129Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P129_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (79 / 200) 0) -
      (momentScalarAmp2622K00P129Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P129Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P129 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P129]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P129 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P129 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P129Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P129Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P129_replay] at h
  simpa only [momentPanelPhase_owner2622K00P129] using h

theorem momentScalarAmp2622K00P129_radius_le :
    (momentScalarAmp2622K00P129Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 87 := by
  norm_num [momentScalarAmp2622K00P129Expected]

def momentScalarGrow2622K00P129Input : RatPair2542 := (momentPanelGrowth2622K00P129 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P129Expected : RatState2542 :=
  ((((1537426209331312617478440655335024368104427245299398447711468096347634633343048530905893385888195 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((974459289956485479210233645096239000367900494541 : ℚ) / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344))

theorem momentScalarGrow2622K00P129_replay :
    compactExp2620 momentScalarGrow2622K00P129Input 20 = momentScalarGrow2622K00P129Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P129_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (79 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P129Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P129Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P129 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P129]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P129 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P129 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P129Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P129Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P129_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P129] using h

theorem momentScalarGrow2622K00P129_radius_le :
    (momentScalarGrow2622K00P129Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P129Expected]

end ConnesWeilRH.Dev
