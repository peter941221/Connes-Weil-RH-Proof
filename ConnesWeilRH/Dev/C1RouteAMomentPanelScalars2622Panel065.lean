import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P065 : ℚ := ((-1860803794101910305413725105104640643591834364763781107 : ℚ) / 57240625064588144605771193776353672141711883003494400)

def momentPanelGrowth2622P065 : ℚ := ((6674677977690233773956355607794940299742475118969 : ℚ) / 34253944624943037145398863266787883273185918976000)

theorem momentPanelPhase_owner2622P065 :
    (momentPanelPhase2622P065 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-49 / 200) 0 := by
  norm_num [momentPanelPhase2622P065, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P065 :
    (momentPanelGrowth2622P065 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-49 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P065, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P065Input : RatPair2542 := (momentPanelPhase2622P065 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P065Expected : RatState2542 :=
  ((((8134478445061713683315362330167042509582789995027067876812851043892462314627952059 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((10311996177035926853831707917264025 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarAmp2622P065_replay :
    compactExp2620 momentScalarAmp2622P065Input 20 = momentScalarAmp2622P065Expected := by
  decide +kernel

theorem momentScalarAmp2622P065_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-49 / 200) 0) -
      (momentScalarAmp2622P065Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P065Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P065 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P065]
  have h := compactExp_real_error2620 momentPanelPhase2622P065 20 hsmall
  change |Real.exp (momentPanelPhase2622P065 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P065Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P065Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P065_replay] at h
  simpa only [momentPanelPhase_owner2622P065] using h

theorem momentScalarAmp2622P065_radius_le :
    (momentScalarAmp2622P065Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 86 := by
  norm_num [momentScalarAmp2622P065Expected]

def momentScalarGrow2622P065Input : RatPair2542 := (momentPanelGrowth2622P065 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P065Expected : RatState2542 :=
  ((((1297760826051674321778155263809270528188753538295029606023626451111644246141001251916451605774669 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((411276746096005592947996140905263437111592478811 : ℚ) / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672))

theorem momentScalarGrow2622P065_replay :
    compactExp2620 momentScalarGrow2622P065Input 20 = momentScalarGrow2622P065Expected := by
  decide +kernel

theorem momentScalarGrow2622P065_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-49 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P065Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P065Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P065 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P065]
  have h := compactExp_real_error2620 momentPanelGrowth2622P065 20 hsmall
  change |Real.exp (momentPanelGrowth2622P065 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P065Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P065Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P065_replay] at h
  simpa only [momentPanelGrowth_owner2622P065] using h

theorem momentScalarGrow2622P065_radius_le :
    (momentScalarGrow2622P065Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P065Expected]

end ConnesWeilRH.Dev
