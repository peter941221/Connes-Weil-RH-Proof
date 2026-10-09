import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K00

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K00P128 : ℚ := ((-1778566110082235381447590649135615703804721668719071681 : ℚ) / 51869606547397076381372652016121332044476330908057600)

def momentPanelGrowth2622K00P128 : ℚ := ((57407889644488569440003614859528619805257729858951046711 : ℚ) / 164175596460707291291569439849192129707711916528789094400)

theorem momentPanelPhase_owner2622K00P128 :
    (momentPanelPhase2622K00P128 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (77 / 200) 0 := by
  norm_num [momentPanelPhase2622K00P128, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K00P128 :
    (momentPanelGrowth2622K00P128 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (77 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622K00P128, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K00P128Input : RatPair2542 := (momentPanelPhase2622K00P128 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K00P128Expected : RatState2542 :=
  ((((2741563654576160974304775562445014499239756947152365025127213745730991105118229521 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1737729231398359429742932246274483 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622K00P128_replay :
    compactExp2620 momentScalarAmp2622K00P128Input 20 = momentScalarAmp2622K00P128Expected := by
  decide +kernel

theorem momentScalarAmp2622K00P128_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (77 / 200) 0) -
      (momentScalarAmp2622K00P128Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K00P128Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K00P128 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622K00P128]
  have h := compactExp_real_error2620 momentPanelPhase2622K00P128 20 hsmall
  change |Real.exp (momentPanelPhase2622K00P128 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K00P128Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K00P128Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K00P128_replay] at h
  simpa only [momentPanelPhase_owner2622K00P128] using h

theorem momentScalarAmp2622K00P128_radius_le :
    (momentScalarAmp2622K00P128Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [momentScalarAmp2622K00P128Expected]

def momentScalarGrow2622K00P128Input : RatPair2542 := (momentPanelGrowth2622K00P128 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K00P128Expected : RatState2542 :=
  ((((3030121022558163966506534684438176158067595422333385977781520211723379993063000111443483050308453 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((3841133452088475789422885422663696882582804119625 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K00P128_replay :
    compactExp2620 momentScalarGrow2622K00P128Input 20 = momentScalarGrow2622K00P128Expected := by
  decide +kernel

theorem momentScalarGrow2622K00P128_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (77 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K00P128Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K00P128Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K00P128 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622K00P128]
  have h := compactExp_real_error2620 momentPanelGrowth2622K00P128 20 hsmall
  change |Real.exp (momentPanelGrowth2622K00P128 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K00P128Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K00P128Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K00P128_replay] at h
  simpa only [momentPanelGrowth_owner2622K00P128] using h

theorem momentScalarGrow2622K00P128_radius_le :
    (momentScalarGrow2622K00P128Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622K00P128Expected]

end ConnesWeilRH.Dev
