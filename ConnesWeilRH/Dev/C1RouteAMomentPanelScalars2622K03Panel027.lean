import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620K03

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622K03P027 : ℚ := ((-117359542414998048843149992498266687811188297128705 : ℚ) / 2374940160662717242080987853163959906940890382336)

def momentPanelGrowth2622K03P027 : ℚ := ((3462633122657472772292688073387773031625097476334676425 : ℚ) / 3322446378504567246163051154792555396181716737768554496)

theorem momentPanelPhase_owner2622K03P027 :
    (momentPanelPhase2622K03P027 : ℝ) = momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-5 / 8) 0 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P027, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622K03P027 :
    (momentPanelGrowth2622K03P027 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2))
      (-5 / 8) (1 / 200) * (1 / 200) := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P027, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622K03P027Input : RatPair2542 := (momentPanelPhase2622K03P027 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622K03P027Expected : RatState2542 :=
  ((((738914230647141007694442301627677932243299317500317918677860584048744738913 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((939147063430014109912222945 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622K03P027_replay :
    compactExp2620 momentScalarAmp2622K03P027Input 20 = momentScalarAmp2622K03P027Expected := by
  decide +kernel

theorem momentScalarAmp2622K03P027_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-5 / 8) 0) -
      (momentScalarAmp2622K03P027Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622K03P027Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622K03P027 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelPhase2622K03P027]
  have h := compactExp_real_error2620 momentPanelPhase2622K03P027 20 hsmall
  change |Real.exp (momentPanelPhase2622K03P027 : ℝ) -
    ((compactExp2620 momentScalarAmp2622K03P027Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622K03P027Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622K03P027_replay] at h
  simpa only [momentPanelPhase_owner2622K03P027] using h

theorem momentScalarAmp2622K03P027_radius_le :
    (momentScalarAmp2622K03P027Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 93 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarAmp2622K03P027Expected]

def momentScalarGrow2622K03P027Input : RatPair2542 := (momentPanelGrowth2622K03P027 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622K03P027Expected : RatState2542 :=
  ((((6056443119000039440715673024181973501171246726740083038195983746737872119558066689543319306625961 : ℚ) / 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576), 0), ((7677446124327464182344729035187070776297041990513 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarGrow2622K03P027_replay :
    compactExp2620 momentScalarGrow2622K03P027Input 20 = momentScalarGrow2622K03P027Expected := by
  decide +kernel

theorem momentScalarGrow2622K03P027_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 3).re * (storedWidth 3 ^ 2)) (-5 / 8) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622K03P027Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622K03P027Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622K03P027 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentPanelGrowth2622K03P027]
  have h := compactExp_real_error2620 momentPanelGrowth2622K03P027 20 hsmall
  change |Real.exp (momentPanelGrowth2622K03P027 : ℝ) -
    ((compactExp2620 momentScalarGrow2622K03P027Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622K03P027Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622K03P027_replay] at h
  simpa only [momentPanelGrowth_owner2622K03P027] using h

theorem momentScalarGrow2622K03P027_radius_le :
    (momentScalarGrow2622K03P027Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 71 := by
  norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, momentScalarGrow2622K03P027Expected]

end ConnesWeilRH.Dev
