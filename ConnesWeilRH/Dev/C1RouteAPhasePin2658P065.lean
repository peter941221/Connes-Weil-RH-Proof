import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 065 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P065 : ℚ := (-355814858691959170035551266699545089080597014775 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P065 : RatPair2542 := ((1130611729711129593310075715255450699602744629249995338986337990156992057777143866660838442196417 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (453056131612146574523258988087051330016669777412495213719356074238346005411015585942671625936663 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P065 : ℚ := (27822135383213212277578246063180083945393979159087 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P065 :
    phaseExp2646 phaseArg2658P065 20 =
      ((phaseValue2658P065.1,
        phaseValue2658P065.2), phaseRadius2658P065) := by
  decide +kernel

theorem phaseCosPin2658P065 :
    |Real.cos (phaseArg2658P065 : ℝ) -
      (phaseValue2658P065.1 : ℝ)| ≤
        (phaseRadius2658P065 : ℝ) := by
  have hsmall : |((phaseArg2658P065 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P065]
  have h := phaseExp_cos_error2646 phaseArg2658P065 20 hsmall
  rw [phaseChain2658P065] at h
  simpa [phaseValue2658P065] using h

theorem phaseSinPin2658P065 :
    |Real.sin (phaseArg2658P065 : ℝ) -
      (phaseValue2658P065.2 : ℝ)| ≤
        (phaseRadius2658P065 : ℝ) := by
  have hsmall : |((phaseArg2658P065 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P065]
  have h := phaseExp_sin_error2646 phaseArg2658P065 20 hsmall
  rw [phaseChain2658P065] at h
  simpa [phaseValue2658P065] using h

end ConnesWeilRH.Dev
