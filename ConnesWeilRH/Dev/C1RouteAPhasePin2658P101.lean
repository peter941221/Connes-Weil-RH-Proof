import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 101 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P101 : ℚ := (78399884118567274753596041815154002678775613425 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P101 : RatPair2542 := ((-1474422613608649518847857844851335952460250735418837735012184665082903179717693050631834845068355 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (386370820432071628293678504820870726638285564093090241468426811991494096082408725113228421844403 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P101 : ℚ := (18908295609612113848375275710902245107213097584977 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P101 :
    phaseExp2646 phaseArg2658P101 20 =
      ((phaseValue2658P101.1,
        phaseValue2658P101.2), phaseRadius2658P101) := by
  decide +kernel

theorem phaseCosPin2658P101 :
    |Real.cos (phaseArg2658P101 : ℝ) -
      (phaseValue2658P101.1 : ℝ)| ≤
        (phaseRadius2658P101 : ℝ) := by
  have hsmall : |((phaseArg2658P101 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P101]
  have h := phaseExp_cos_error2646 phaseArg2658P101 20 hsmall
  rw [phaseChain2658P101] at h
  simpa [phaseValue2658P101] using h

theorem phaseSinPin2658P101 :
    |Real.sin (phaseArg2658P101 : ℝ) -
      (phaseValue2658P101.2 : ℝ)| ≤
        (phaseRadius2658P101 : ℝ) := by
  have hsmall : |((phaseArg2658P101 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P101]
  have h := phaseExp_sin_error2646 phaseArg2658P101 20 hsmall
  rw [phaseChain2658P101] at h
  simpa [phaseValue2658P101] using h

end ConnesWeilRH.Dev
