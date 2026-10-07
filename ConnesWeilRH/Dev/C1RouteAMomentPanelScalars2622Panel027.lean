import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P027 : ℚ := ((-120511040509394262561241790483998477197322498208695 : ℚ) / 2374940160662717242080987853163959906940890382336)

def momentPanelGrowth2622P027 : ℚ := ((88329356024576016232175939720154340126043948241422820631 : ℚ) / 83061159462614181154076278869813884904542918444213862400)

theorem momentPanelPhase_owner2622P027 :
    (momentPanelPhase2622P027 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-5 / 8) 0 := by
  norm_num [momentPanelPhase2622P027, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P027 :
    (momentPanelGrowth2622P027 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (-5 / 8) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P027, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P027Input : RatPair2542 := (momentPanelPhase2622P027 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P027Expected : RatState2542 :=
  ((((196017090692935245439841449394144003263793297746969990655646053156731558913 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((250911059122333143181675667 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P027_replay :
    compactExp2620 momentScalarAmp2622P027Input 20 = momentScalarAmp2622P027Expected := by
  decide +kernel

theorem momentScalarAmp2622P027_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-5 / 8) 0) -
      (momentScalarAmp2622P027Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P027Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P027 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P027]
  have h := compactExp_real_error2620 momentPanelPhase2622P027 20 hsmall
  change |Real.exp (momentPanelPhase2622P027 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P027Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P027Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P027_replay] at h
  simpa only [momentPanelPhase_owner2622P027] using h

theorem momentScalarAmp2622P027_radius_le :
    (momentScalarAmp2622P027Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 94 := by
  norm_num [momentScalarAmp2622P027Expected]

def momentScalarGrow2622P027Input : RatPair2542 := (momentPanelGrowth2622P027 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P027Expected : RatState2542 :=
  ((((6186406368221818103938109907461573910936309633992441895522558651441690510859744135910864565824925 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7842193792676305845534990830703486390920387449673 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622P027_replay :
    compactExp2620 momentScalarGrow2622P027Input 20 = momentScalarGrow2622P027Expected := by
  decide +kernel

theorem momentScalarGrow2622P027_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (-5 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P027Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P027Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P027 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P027]
  have h := compactExp_real_error2620 momentPanelGrowth2622P027 20 hsmall
  change |Real.exp (momentPanelGrowth2622P027 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P027Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P027Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P027_replay] at h
  simpa only [momentPanelGrowth_owner2622P027] using h

theorem momentScalarGrow2622P027_radius_le :
    (momentScalarGrow2622P027Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [momentScalarGrow2622P027Expected]

end ConnesWeilRH.Dev
