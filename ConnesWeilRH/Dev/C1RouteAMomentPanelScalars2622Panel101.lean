import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P101 : ℚ := ((-1810159374022998522378034998016820028196518043574914219 : ℚ) / 60090553257383405296268379200150424030040951462297600)

def momentPanelGrowth2622P101 : ℚ := ((1331079727186258203880350182663631797303321306076559 : ℚ) / 13539442512085817815671324020585690661781287573913600)

theorem momentPanelPhase_owner2622P101 :
    (momentPanelPhase2622P101 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (23 / 200) 0 := by
  norm_num [momentPanelPhase2622P101, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P101 :
    (momentPanelGrowth2622P101 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (23 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P101, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P101Input : RatPair2542 := (momentPanelPhase2622P101 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P101Expected : RatState2542 :=
  ((((2759260813674004806363070244141912927700145881380383880250468671771395775627464657 : ℚ) / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384), 0), ((223864263266127921574486447304699725 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P101_replay :
    compactExp2620 momentScalarAmp2622P101Input 20 = momentScalarAmp2622P101Expected := by
  decide +kernel

theorem momentScalarAmp2622P101_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (23 / 200) 0) -
      (momentScalarAmp2622P101Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P101Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P101 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P101]
  have h := compactExp_real_error2620 momentPanelPhase2622P101 20 hsmall
  change |Real.exp (momentPanelPhase2622P101 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P101Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P101Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P101_replay] at h
  simpa only [momentPanelPhase_owner2622P101] using h

theorem momentScalarAmp2622P101_radius_le :
    (momentScalarAmp2622P101Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 85 := by
  norm_num [momentScalarAmp2622P101Expected]

def momentScalarGrow2622P101Input : RatPair2542 := (momentPanelGrowth2622P101 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P101Expected : RatState2542 :=
  ((((2356647638989775990274783931470398398471576587587400402651418272529541018805111455805267720899873 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((1493702757000924886000650287272115730347181640267 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622P101_replay :
    compactExp2620 momentScalarGrow2622P101Input 20 = momentScalarGrow2622P101Expected := by
  decide +kernel

theorem momentScalarGrow2622P101_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (23 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P101Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P101Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P101 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P101]
  have h := compactExp_real_error2620 momentPanelGrowth2622P101 20 hsmall
  change |Real.exp (momentPanelGrowth2622P101 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P101Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P101Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P101_replay] at h
  simpa only [momentPanelGrowth_owner2622P101] using h

theorem momentScalarGrow2622P101_radius_le :
    (momentScalarGrow2622P101Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P101Expected]

end ConnesWeilRH.Dev
