import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P163 : ℚ := ((-5331278196847798582055282566185703514362717620609570333 : ℚ) / 83995239412976986152137399245266128170288298118348800)

def momentPanelGrowth2622K00P163 : ℚ := ((2135882233493284550488894590750004144378342223636280277 : ℚ) / 973695779119705785287679007449059012346928295627980800)

theorem momentPanelPhase_owner2622K00P163 :
    (momentPanelPhase2622K00P163 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (147 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P163, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P163 :
    (momentPanelGrowth2622K00P163 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (147 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P163, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P163Input : RatPair2542 := (momentPanelPhase2622K00P163 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P163Expected : RatState2542 :=
  ((((581311591674794444814189565408785689738394536623121176515014744969405 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((2418588583823975676158039 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P163_replay :
    compactExp2620 momentScalarAmp2622K00P163Input 20 = momentScalarAmp2622K00P163Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P163_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (147 / 200) 0) -
      (momentScalarAmp2622K00P163Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P163Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P163 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P163]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P163 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P163 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P163Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P163Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P163_replay] at h
  simpa only [momentPanelPhase_owner2622K00P163] using h

theorem momentScalarAmp2622K00P163_radius_le :
    (momentScalarAmp2622K00P163Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622K00P163Expected]

def momentScalarGrow2622K00P163Input : RatPair2542 := (momentPanelGrowth2622K00P163 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P163Expected : RatState2542 :=
  ((((9576999985411913532585527608462108547838667487992331483405032881392232877095085021920844710911511 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((3035066095719158966108835536797273300161962396893 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622K00P163_replay :
    compactExp2620 momentScalarGrow2622K00P163Input 20 = momentScalarGrow2622K00P163Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P163_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (147 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P163Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P163Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P163 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P163]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P163 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P163 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P163Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P163Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P163_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P163] using h

theorem momentScalarGrow2622K00P163_radius_le :
    (momentScalarGrow2622K00P163Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P163Expected]

end ConnesWeilRH.Dev
