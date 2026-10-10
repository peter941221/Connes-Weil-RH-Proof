import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 093 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P093 : ℚ := (-18092280950438601866214471188112462156640526175 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P093 : RatPair2542 := ((2132758805206450032375964202318124440330442776631646562656815592608042017196706393944376137021683 / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), (-29347589803669296500445843603144338658129086443873386797775323342430677964649458876515792967059 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144))
def phaseRadius2658P093 : ℚ := (3696716152093718818503152586076645783873808077563 / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688)

theorem phaseChain2658P093 :
    phaseExp2646 phaseArg2658P093 20 =
      ((phaseValue2658P093.1,
        phaseValue2658P093.2), phaseRadius2658P093) := by
  decide +kernel

theorem phaseCosPin2658P093 :
    |Real.cos (phaseArg2658P093 : ℝ) -
      (phaseValue2658P093.1 : ℝ)| ≤
        (phaseRadius2658P093 : ℝ) := by
  have hsmall : |((phaseArg2658P093 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P093]
  have h := phaseExp_cos_error2646 phaseArg2658P093 20 hsmall
  rw [phaseChain2658P093] at h
  simpa [phaseValue2658P093] using h

theorem phaseSinPin2658P093 :
    |Real.sin (phaseArg2658P093 : ℝ) -
      (phaseValue2658P093.2 : ℝ)| ≤
        (phaseRadius2658P093 : ℝ) := by
  have hsmall : |((phaseArg2658P093 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P093]
  have h := phaseExp_sin_error2646 phaseArg2658P093 20 hsmall
  rw [phaseChain2658P093] at h
  simpa [phaseValue2658P093] using h

end ConnesWeilRH.Dev
