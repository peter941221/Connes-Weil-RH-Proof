import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 058 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P058 : ℚ := (-440245503127339312077885465577403245811586136925 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P058 : RatPair2542 := ((-1023154572153282989307788054937527753473186904374274105458426278958967048623411523899515848080931 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (153105254553347415474588196146813698049364628643748660573403189881512919548993550798149445308999 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P058 : ℚ := (31391015587766187890374762279222759595480590847219 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P058 :
    phaseExp2646 phaseArg2658P058 20 =
      ((phaseValue2658P058.1,
        phaseValue2658P058.2), phaseRadius2658P058) := by
  decide +kernel

theorem phaseCosPin2658P058 :
    |Real.cos (phaseArg2658P058 : ℝ) -
      (phaseValue2658P058.1 : ℝ)| ≤
        (phaseRadius2658P058 : ℝ) := by
  have hsmall : |((phaseArg2658P058 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P058]
  have h := phaseExp_cos_error2646 phaseArg2658P058 20 hsmall
  rw [phaseChain2658P058] at h
  simpa [phaseValue2658P058] using h

theorem phaseSinPin2658P058 :
    |Real.sin (phaseArg2658P058 : ℝ) -
      (phaseValue2658P058.2 : ℝ)| ≤
        (phaseRadius2658P058 : ℝ) := by
  have hsmall : |((phaseArg2658P058 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P058]
  have h := phaseExp_sin_error2646 phaseArg2658P058 20 hsmall
  rw [phaseChain2658P058] at h
  simpa [phaseValue2658P058] using h

end ConnesWeilRH.Dev
