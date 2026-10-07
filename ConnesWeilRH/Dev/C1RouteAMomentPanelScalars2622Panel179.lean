import ConnesWeilRH.Dev.C1RouteACompactExpSharp3202620
import ConnesWeilRH.Dev.C1RouteAMomentScalarOwner2620

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

def momentPanelPhase2622P179 : ℚ := ((-1800642027423445976438283458968529385456421183274876223 : ℚ) / 12116762011996517006232424566238433909834965739110400)

def momentPanelGrowth2622P179 : ℚ := ((12351363424022183410911065674441748696201855293086031 : ℚ) / 824378267306962427299265975954028390774674450022400)

theorem momentPanelPhase_owner2622P179 :
    (momentPanelPhase2622P179 : ℝ) = momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (179 / 200) 0 := by
  norm_num [momentPanelPhase2622P179, momentPhase2619, capturedNodes2584, storedWidth]

theorem momentPanelGrowth_owner2622P179 :
    (momentPanelGrowth2622P179 : ℝ) = 2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2))
      (179 / 200) (1 / 200) * (1 / 200) := by
  norm_num [momentPanelGrowth2622P179, momentPhaseSlopeUpper2619, capturedNodes2584, storedWidth]

def momentScalarAmp2622P179Input : RatPair2542 := (momentPanelPhase2622P179 / (2 : ℚ) ^ 20, 0)

def momentScalarAmp2622P179Expected : RatState2542 :=
  ((((30841823334475449340975482006571 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((2417851639229258349412353 : ℚ) / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376))

theorem momentScalarAmp2622P179_replay :
    compactExp2620 momentScalarAmp2622P179Input 20 = momentScalarAmp2622P179Expected := by
  decide +kernel

theorem momentScalarAmp2622P179_error :
    |Real.exp (momentPhase2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (179 / 200) 0) -
      (momentScalarAmp2622P179Expected.1.1 : ℝ)| ≤
      (momentScalarAmp2622P179Expected.2 : ℝ) := by
  have hsmall : |((momentPanelPhase2622P179 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelPhase2622P179]
  have h := compactExp_real_error2620 momentPanelPhase2622P179 20 hsmall
  change |Real.exp (momentPanelPhase2622P179 : ℝ) -
    ((compactExp2620 momentScalarAmp2622P179Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarAmp2622P179Input 20).2 : ℝ) at h
  rw [momentScalarAmp2622P179_replay] at h
  simpa only [momentPanelPhase_owner2622P179] using h

theorem momentScalarAmp2622P179_radius_le :
    (momentScalarAmp2622P179Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 96 := by
  norm_num [momentScalarAmp2622P179Expected]

def momentScalarGrow2622P179Input : RatPair2542 := (momentPanelGrowth2622P179 / (2 : ℚ) ^ 20, 0)

def momentScalarGrow2622P179Expected : RatState2542 :=
  ((((3431206218959439287885825646326603430339676550949543112880047858787843293981524989131536153596226734233 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288), 0), ((4349508474315353005143956953624953903650210503357456291 : ℚ) / 1291124939043454294827959586001505937164852896414611756415329678270323811008420597314822676640068915717951585986373746688))

theorem momentScalarGrow2622P179_replay :
    compactExp2620 momentScalarGrow2622P179Input 20 = momentScalarGrow2622P179Expected := by
  decide +kernel

theorem momentScalarGrow2622P179_error :
    |Real.exp (2 * momentPhaseSlopeUpper2619 ((capturedNodes2584 0).re * (storedWidth 0 ^ 2)) (179 / 200) (1 / 200) *
      (1 / 200)) -
      (momentScalarGrow2622P179Expected.1.1 : ℝ)| ≤
      (momentScalarGrow2622P179Expected.2 : ℝ) := by
  have hsmall : |((momentPanelGrowth2622P179 / (2 : ℚ) ^ 20 : ℚ) : ℝ)| ≤ (1 : ℝ) / 1000 := by
    norm_num [momentPanelGrowth2622P179]
  have h := compactExp_real_error2620 momentPanelGrowth2622P179 20 hsmall
  change |Real.exp (momentPanelGrowth2622P179 : ℝ) -
    ((compactExp2620 momentScalarGrow2622P179Input 20).1.1 : ℝ)| ≤
      ((compactExp2620 momentScalarGrow2622P179Input 20).2 : ℝ) at h
  rw [momentScalarGrow2622P179_replay] at h
  simpa only [momentPanelGrowth_owner2622P179] using h

theorem momentScalarGrow2622P179_radius_le :
    (momentScalarGrow2622P179Expected.2 : ℝ) ≤ (1 : ℝ) / 10 ^ 65 := by
  norm_num [momentScalarGrow2622P179Expected]

end ConnesWeilRH.Dev
