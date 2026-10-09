import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P167 : ℚ := ((-14250235210542042133114308842058328617622853904061987 : ℚ) / 194562405469676450985865543355355176991696019783680)

def momentPanelGrowth2622K00P167 : ℚ := ((6732468046695567820235463126762096059688405602040661711 : ℚ) / 2188692329351668630978215460552229708815705691285094400)

theorem momentPanelPhase_owner2622K00P167 :
    (momentPanelPhase2622K00P167 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (31 / 40) 0 := by
  norm_num [momentPanelPhase2622K00P167, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P167 :
    (momentPanelGrowth2622K00P167 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (31 / 40) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P167, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P167Input : RatPair2542 := (momentPanelPhase2622K00P167 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P167Expected : RatState2542 :=
  ((((16586661495211557727167412975018498710368187873570304095937390467 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851681284379178214251 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P167_replay :
    compactExp2620 momentScalarAmp2622K00P167Input 20 = momentScalarAmp2622K00P167Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P167_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (31 / 40) 0) -
      (momentScalarAmp2622K00P167Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P167Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P167 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P167]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P167 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P167 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P167Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P167Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P167_replay] at h
  simpa only [momentPanelPhase_owner2622K00P167] using h

theorem momentScalarAmp2622K00P167_radius_le :
    (momentScalarAmp2622K00P167Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622K00P167Expected]

def momentScalarGrow2622K00P167Input : RatPair2542 := (momentPanelGrowth2622K00P167 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P167Expected : RatState2542 :=
  ((((23145600462476110677591449454763572049448625144023657761150357867605979560162554526520364784263477 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((1833778015491256775351720157672316800562866084271 : ℚ) / 80695308690215893426747474125094121072803306025913234775958104891895238188026287332176417290004307232371974124148359168))

theorem momentScalarGrow2622K00P167_replay :
    compactExp2620 momentScalarGrow2622K00P167Input 20 = momentScalarGrow2622K00P167Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P167_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (31 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P167Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P167Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P167 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P167]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P167 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P167 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P167Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P167Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P167_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P167] using h

theorem momentScalarGrow2622K00P167_radius_le :
    (momentScalarGrow2622K00P167Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 70 := by
  norm_num [momentScalarGrow2622K00P167Expected]

end ConnesWeilRH.Dev
