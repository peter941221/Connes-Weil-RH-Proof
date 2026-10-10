import ConnesWeilRH.Dev.C1RouteAComplexPhaseEngine2646

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

/-! Exact rotation pin for panel 067 of entry (0, 3), record 2658.
The rotation is exp(i * psi * center) and uses the already certified
record-2646 compact exponential engine. -/

def phaseArg2658P067 : ℚ := (-331691817424707700880598638448728472871742979875 / 2854495385411919762116571938898990272765493248)
def phaseValue2658P067 : RatPair2542 := ((-1067176424488492265944332018762638533196059701031352445231985025442019709970839905662063649408581 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), (-41768809194256057668227239771383180841132083727454647139420025440927729568203368858604984452935 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288))
def phaseRadius2658P067 : ℚ := (32196992000591185548702300938815655377988942760207 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376)

theorem phaseChain2658P067 :
    phaseExp2646 phaseArg2658P067 20 =
      ((phaseValue2658P067.1,
        phaseValue2658P067.2), phaseRadius2658P067) := by
  decide +kernel

theorem phaseCosPin2658P067 :
    |Real.cos (phaseArg2658P067 : ℝ) -
      (phaseValue2658P067.1 : ℝ)| ≤
        (phaseRadius2658P067 : ℝ) := by
  have hsmall : |((phaseArg2658P067 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P067]
  have h := phaseExp_cos_error2646 phaseArg2658P067 20 hsmall
  rw [phaseChain2658P067] at h
  simpa [phaseValue2658P067] using h

theorem phaseSinPin2658P067 :
    |Real.sin (phaseArg2658P067 : ℝ) -
      (phaseValue2658P067.2 : ℝ)| ≤
        (phaseRadius2658P067 : ℝ) := by
  have hsmall : |((phaseArg2658P067 / (2 : ℚ) ^ 20 : ℚ) : ℝ)|
      ≤ (1 : ℝ) / 1000 := by
    norm_num [phaseArg2658P067]
  have h := phaseExp_sin_error2646 phaseArg2658P067 20 hsmall
  rw [phaseChain2658P067] at h
  simpa [phaseValue2658P067] using h

end ConnesWeilRH.Dev
