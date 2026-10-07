import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P115 : ℚ := ((-5375260098642642723397794078407008471660239232424034621 : ℚ) / 170808436670432619493436278308613339537850691171123200)

def momentPanelGrowth2622P115 : ℚ := ((842227394762369617050334074764648708424587998109321077 : ℚ) / 4136019946894446974550902064238916396127452335492300800)

theorem momentPanelPhase_owner2622P115 :
    (momentPanelPhase2622P115 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (51 / 200) 0 := by
  norm_num [momentPanelPhase2622P115, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P115 :
    (momentPanelGrowth2622P115 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (51 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P115, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P115Input : RatPair2542 := (momentPanelPhase2622P115 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P115Expected : RatState2542 :=
  ((((45978864508058704872192628317398050366084575997400485448819685388659854441792014675 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((29143442227363377230402674390463283 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622P115_replay :
    compactExp2620 momentScalarAmp2622P115Input 20 = momentScalarAmp2622P115Expected := by
  decide +kernel

theorem momentScalarAmp2622P115_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (51 / 200) 0) -
      (momentScalarAmp2622P115Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P115Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P115 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P115]
  have h := compactExp_real_error2620 momentPanelPhase2622P115 20 hsmall
  change |Real.exp (momentPanelPhase2622P115 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P115Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P115Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P115_replay] at h
  simpa only [momentPanelPhase_owner2622P115] using h

theorem momentScalarAmp2622P115_radius_le :
    (momentScalarAmp2622P115Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622P115Expected]

def momentScalarGrow2622P115Input : RatPair2542 := (momentPanelGrowth2622P115 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P115Expected : RatState2542 :=
  ((((2618394086166382861068964324077436157825447840703690675727744762498144335870433417971628060141133 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3319208190376130486370066518643613147990629742529 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P115_replay :
    compactExp2620 momentScalarGrow2622P115Input 20 = momentScalarGrow2622P115Expected := by
  decide +kernel

theorem momentScalarGrow2622P115_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (51 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P115Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P115Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P115 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P115]
  have h := compactExp_real_error2620 momentPanelGrowth2622P115 20 hsmall
  change |Real.exp (momentPanelGrowth2622P115 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P115Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P115Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P115_replay] at h
  simpa only [momentPanelGrowth_owner2622P115] using h

theorem momentScalarGrow2622P115_radius_le :
    (momentScalarGrow2622P115Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P115Expected]

end ConnesWeilRH.Dev
