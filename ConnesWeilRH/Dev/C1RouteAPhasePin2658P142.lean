import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 142 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P142 : ℚ := (572922230097222392430124920956894634960283328875 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P142 : RatPair2542 := ((2004156420604522303165792458033393770078817555666323007897190775325659591831043094465409898806009 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-369390599288836906788807718639212732051632656660161445914055599847562225249808905807260216028221 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P142 : ℚ := (9656855431439923701256525214099434356054710189113 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P142 :
    phaseExp2646 phaseArg2658P142 20 =
      ((phaseValue2658P142.1,
        phaseValue2658P142.2), phaseRadius2658P142) := by
  decide +kernel

theorem phaseCosPin2658P142 :
    |Real.cos (phaseArg2658P142 : ℝ) -
      (phaseValue2658P142.1 : ℝ)| ≤
        (phaseRadius2658P142 : ℝ) := by
  have hsmall : |((phaseArg2658P142 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P142]
  have h := phaseExp_cos_error2646 phaseArg2658P142 20 hsmall
  rw [phaseChain2658P142] at h
  simpa [phaseValue2658P142] using h

theorem phaseSinPin2658P142 :
    |Real.sin (phaseArg2658P142 : ℝ) -
      (phaseValue2658P142.2 : ℝ)| ≤
        (phaseRadius2658P142 : ℝ) := by
  have hsmall : |((phaseArg2658P142 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P142]
  have h := phaseExp_sin_error2646 phaseArg2658P142 20 hsmall
  rw [phaseChain2658P142] at h
  simpa [phaseValue2658P142] using h

end ConnesWeilRH.Dev
