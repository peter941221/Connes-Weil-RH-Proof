import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P074 : ℚ := ((-1849162949344787344785728136292841469624846683245390813 : ℚ) / 59432877520584498983076721025428096671195781817958400)

def momentPanelGrowth2622K00P074 : ℚ := ((35374698032431223654354692420189996124471404584720317 : ℚ) / 282314160809855523544948351272212376360943707016396800)

theorem momentPanelPhase_owner2622K00P074 :
    (momentPanelPhase2622K00P074 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-31 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P074, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P074 :
    (momentPanelGrowth2622K00P074 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-31 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P074, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P074Input : RatPair2542 := (momentPanelPhase2622K00P074 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P074Expected : RatState2542 :=
  ((((65643393904761665964209864633047834282351166728972711163829385142486893055971793319 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((83215356825861136983934050351188259 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K00P074_replay :
    compactExp2620 momentScalarAmp2622K00P074Input 20 = momentScalarAmp2622K00P074Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P074_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-31 / 200) 0) -
      (momentScalarAmp2622K00P074Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P074Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P074 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P074]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P074 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P074 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P074Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P074Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P074_replay] at h
  simpa only [momentPanelPhase_owner2622K00P074] using h

theorem momentScalarAmp2622K00P074_radius_le :
    (momentScalarAmp2622K00P074Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622K00P074Expected]

def momentScalarGrow2622K00P074Input : RatPair2542 := (momentPanelGrowth2622K00P074 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P074Expected : RatState2542 :=
  ((((2421122923622923813530779698135988726531065529680422181452550182203967822191145917104138756219391 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3069137560601501065032840556862763621266750071535 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P074_replay :
    compactExp2620 momentScalarGrow2622K00P074Input 20 = momentScalarGrow2622K00P074Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P074_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-31 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P074Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P074Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P074 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P074]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P074 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P074 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P074Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P074Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P074_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P074] using h

theorem momentScalarGrow2622K00P074_radius_le :
    (momentScalarGrow2622K00P074Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P074Expected]

end ConnesWeilRH.Dev
