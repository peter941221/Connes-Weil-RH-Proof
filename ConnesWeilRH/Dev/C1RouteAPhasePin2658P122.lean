import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 122 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P122 : ℚ := (331691817424707700880598638448728472871742979875 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P122 : RatPair2542 := ((-266794106122123066486083004690659633299014925257838111307996256360504927492709976415515912340095 / 266998379490113760299377713271194014325338065294581596243380200977777465722580068752870260867072), (1305275287320501802132101242855724401285377616482957723106875795028991549006355276831405796891 / 33374797436264220037422214158899251790667258161822699530422525122222183215322508594108782608384))
def phaseRadius2658P122 : ℚ := (32196992000591185548702300938815655377988942760207 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P122 :
    phaseExp2646 phaseArg2658P122 20 =
      ((phaseValue2658P122.1,
        phaseValue2658P122.2), phaseRadius2658P122) := by
  decide +kernel

theorem phaseCosPin2658P122 :
    |Real.cos (phaseArg2658P122 : ℝ) -
      (phaseValue2658P122.1 : ℝ)| ≤
        (phaseRadius2658P122 : ℝ) := by
  have hsmall : |((phaseArg2658P122 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P122]
  have h := phaseExp_cos_error2646 phaseArg2658P122 20 hsmall
  rw [phaseChain2658P122] at h
  simpa [phaseValue2658P122] using h

theorem phaseSinPin2658P122 :
    |Real.sin (phaseArg2658P122 : ℝ) -
      (phaseValue2658P122.2 : ℝ)| ≤
        (phaseRadius2658P122 : ℝ) := by
  have hsmall : |((phaseArg2658P122 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P122]
  have h := phaseExp_sin_error2646 phaseArg2658P122 20 hsmall
  rw [phaseChain2658P122] at h
  simpa [phaseValue2658P122] using h

end ConnesWeilRH.Dev
