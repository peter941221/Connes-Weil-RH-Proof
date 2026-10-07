import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P047 : ℚ := ((-15025429709398071554662252815250266548205402510543059 : ℚ) / 399172634696002859534381419935634799743526575800320)

def momentPanelGrowth2622P047 : ℚ := ((20862393498825913759360897531653951284872644499746823757 : ℚ) / 50573133564480224027528069826851779688853953485524172800)

theorem momentPanelPhase_owner2622P047 :
    (momentPanelPhase2622P047 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-17 / 40) 0 := by
  norm_num [momentPanelPhase2622P047, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P047 :
    (momentPanelGrowth2622P047 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-17 / 40) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P047, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P047Input : RatPair2542 := (momentPanelPhase2622P047 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P047Expected : RatState2542 :=
  ((((95969287118733688933677325714411862133715860838049469482026655669530507685867143 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((121659894065307951260420286787301 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P047_replay :
    compactExp2620 momentScalarAmp2622P047Input 20 = momentScalarAmp2622P047Expected := by
  decide +kernel

theorem momentScalarAmp2622P047_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-17 / 40) 0) -
      (momentScalarAmp2622P047Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P047Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P047 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P047]
  have h := compactExp_real_error2620 momentPanelPhase2622P047 20 hsmall
  change |Real.exp (momentPanelPhase2622P047 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P047Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P047Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P047_replay] at h
  simpa only [momentPanelPhase_owner2622P047] using h

theorem momentScalarAmp2622P047_radius_le :
    (momentScalarAmp2622P047Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 88 := by
  norm_num [momentScalarAmp2622P047Expected]

def momentScalarGrow2622P047Input : RatPair2542 := (momentPanelGrowth2622P047 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P047Expected : RatState2542 :=
  ((((3226661942860937419690007930055853111857698967595768840172407372926682215297859045347633520983039 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((4090278339448385378899070463130211198747226975399 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P047_replay :
    compactExp2620 momentScalarGrow2622P047Input 20 = momentScalarGrow2622P047Expected := by
  decide +kernel

theorem momentScalarGrow2622P047_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-17 / 40) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P047Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P047Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P047 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P047]
  have h := compactExp_real_error2620 momentPanelGrowth2622P047 20 hsmall
  change |Real.exp (momentPanelGrowth2622P047 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P047Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P047Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P047_replay] at h
  simpa only [momentPanelGrowth_owner2622P047] using h

theorem momentScalarGrow2622P047_radius_le :
    (momentScalarGrow2622P047Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P047Expected]

end ConnesWeilRH.Dev
