import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P105 : ℚ := ((-1804591143982469950723483945497866079514984674194609187 : ℚ) / 59432877520584498983076721025428096671195781817958400)

def momentPanelGrowth2622P105 : ℚ := ((35374698032431223654354692420189996124471404584720317 : ℚ) / 282314160809855523544948351272212376360943707016396800)

theorem momentPanelPhase_owner2622P105 :
    (momentPanelPhase2622P105 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (31 / 200) 0 := by
  norm_num [momentPanelPhase2622P105, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P105 :
    (momentPanelGrowth2622P105 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (31 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P105, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P105Input : RatPair2542 := (momentPanelPhase2622P105 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P105Expected : RatState2542 :=
  ((((69480197863906470052067817268090539253586220659690163484983212720055770100414895631 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((11009895623813456873092409234525241 : ℚ) / 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336))

theorem momentScalarAmp2622P105_replay :
    compactExp2620 momentScalarAmp2622P105Input 20 = momentScalarAmp2622P105Expected := by
  decide +kernel

theorem momentScalarAmp2622P105_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (31 / 200) 0) -
      (momentScalarAmp2622P105Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P105Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P105 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P105]
  have h := compactExp_real_error2620 momentPanelPhase2622P105 20 hsmall
  change |Real.exp (momentPanelPhase2622P105 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P105Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P105Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P105_replay] at h
  simpa only [momentPanelPhase_owner2622P105] using h

theorem momentScalarAmp2622P105_radius_le :
    (momentScalarAmp2622P105Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622P105Expected]

def momentScalarGrow2622P105Input : RatPair2542 := (momentPanelGrowth2622P105 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P105Expected : RatState2542 :=
  ((((2421122923622923813530779698135988726531065529680422181452550182203967822191145917104138756219391 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3069137560601501065032840556862763621266750071535 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P105_replay :
    compactExp2620 momentScalarGrow2622P105Input 20 = momentScalarGrow2622P105Expected := by
  decide +kernel

theorem momentScalarGrow2622P105_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (31 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P105Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P105Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P105 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P105]
  have h := compactExp_real_error2620 momentPanelGrowth2622P105 20 hsmall
  change |Real.exp (momentPanelGrowth2622P105 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P105Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P105Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P105_replay] at h
  simpa only [momentPanelGrowth_owner2622P105] using h

theorem momentScalarGrow2622P105_radius_le :
    (momentScalarGrow2622P105Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P105Expected]

end ConnesWeilRH.Dev
